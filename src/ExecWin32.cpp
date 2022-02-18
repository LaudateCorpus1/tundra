/* exec-win32.c -- Windows subprocess handling
 *
 * This module is complicated due to how Win32 handles child I/O and because
 * its command processor cannot handle long command lines, requiring tools to
 * support so-called "response files" which are basically just the contents of
 * the command line, but written to a file. Tundra implements this via the
 * @RESPONSE handling.
 */

#include "Exec.hpp"
#include "Common.hpp"
#include "Config.hpp"
#include "BuildQueue.hpp"
#include "Atomic.hpp"
#include "SignalHandler.hpp"
#include "NodeResultPrinting.hpp"

#include <algorithm>

#if defined(TUNDRA_WIN32)

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>
#include <RestartManager.h>
#include <VersionHelpers.h>
#include <thread>
#include <vector>


// Size of the char array that we create for async IO.
#define PIPE_BUF_SIZE 4096

// Initial capacity of the vector<char> that we create to dynamically buffer output.
#define INITIAL_BUFFER_CAPACITY 4096

static char s_TemporaryDir[MAX_PATH];
static DWORD s_TundraPid;

#define CROAK(...) { PrintMessage(MessageStatusLevel::Warning, __VA_ARGS__); exit(BuildResult::kBuildError); }

static void CopyOutputIntoBuffer(int job_id, const char *command_that_just_finished, OutputBufferData *outputBuffer, MemAllocHeap *heap, std::vector<char> &pipeBuf)
{
    assert(outputBuffer->buffer == nullptr);
    assert(outputBuffer->heap == nullptr);

    outputBuffer->buffer = static_cast<char *>(HeapAllocate(heap, pipeBuf.size() + 1));
    memcpy(outputBuffer->buffer, pipeBuf.data(), pipeBuf.size());
    outputBuffer->buffer[pipeBuf.size()] = '\0';

    outputBuffer->heap = heap;
    outputBuffer->cursor = pipeBuf.size();
    outputBuffer->buffer_size = pipeBuf.size();
}

static struct Win32EnvBinding
{
    const char *m_Name;
    const char *m_Value;
    size_t m_NameLength;
} g_Win32Env[1024];

static char UTF8_WindowsEnvironment[128 * 1024];

static size_t g_Win32EnvCount;

void ExecInit(void)
{
    s_TundraPid = GetCurrentProcessId();

    if (0 == GetTempPathA(sizeof(s_TemporaryDir), s_TemporaryDir))
        CroakErrno("couldn't get temporary directory path");

    // Initialize win32 env block. We're going to let it leak.
    // This block contains a series of nul-terminated strings, with a double nul
    // terminator to indicated the end of the data.

    // Since all our operations are in UTF8 space, we're going to convert the windows environment once on startup into utf8 as well,
    // so that all follow up operations are fast.
    WCHAR *widecharenv = GetEnvironmentStringsW();
    int len = 0;
    while ((*(widecharenv + len)) != 0 || (*(widecharenv + len + 1)) != 0)
        len++;
    len += 2;
    WideCharToMultiByte(CP_UTF8, 0, widecharenv, len, UTF8_WindowsEnvironment, sizeof UTF8_WindowsEnvironment, NULL, NULL);

    const char *env = UTF8_WindowsEnvironment;
    size_t env_count = 0;

    while (*env && env_count < ARRAY_SIZE(g_Win32Env))
    {
        size_t len = strlen(env);

        if (const char *eq = strchr(env, '='))
        {
            // Discard empty variables that Windows sometimes has internally
            if (eq != env)
            {
                g_Win32Env[env_count].m_Name = env;
                g_Win32Env[env_count].m_Value = eq + 1;
                g_Win32Env[env_count].m_NameLength = size_t(eq - env);
                ++env_count;
            }
        }

        env += len + 1;
    }

    g_Win32EnvCount = env_count;
}

static bool
AppendEnvVar(char *block, size_t block_size, size_t *cursor, const char *name, size_t name_len, const char *value)
{
    size_t value_len = strlen(value);
    size_t pos = *cursor;

    if (pos + name_len + value_len + 2 > block_size)
        return false;

    memcpy(block + pos, name, name_len);
    pos += name_len;

    block[pos++] = '=';
    memcpy(block + pos, value, value_len);
    pos += value_len;

    block[pos++] = '\0';

    *cursor = pos;
    return true;
}

extern char *s_Win32EnvBlock;

static bool
MakeEnvBlock(char *env_block, size_t block_size, const EnvVariable *env_vars, int env_count, size_t *out_env_block_length)
{
    size_t cursor = 0;
    size_t env_var_len[ARRAY_SIZE(g_Win32Env)];
    unsigned char used_env[ARRAY_SIZE(g_Win32Env)];

    if (env_count > int(sizeof used_env))
        return false;

    for (int i = 0; i < env_count; ++i)
    {
        env_var_len[i] = strlen(env_vars[i].m_Name);
    }

    memset(used_env, 0, sizeof(used_env));

    // Loop through windows environment block and emit anything we're not going to override.
    for (size_t i = 0, count = g_Win32EnvCount; i < count; ++i)
    {
        bool replaced = false;

        for (int x = 0; !replaced && x < env_count; ++x)
        {
            if (used_env[x])
                continue;

            size_t len = env_var_len[x];
            if (len == g_Win32Env[i].m_NameLength && 0 == _memicmp(g_Win32Env[i].m_Name, env_vars[x].m_Name, len))
            {
                if (!AppendEnvVar(env_block, block_size, &cursor, env_vars[x].m_Name, len, env_vars[x].m_Value))
                    return false;
                replaced = true;
                used_env[x] = 1;
            }
        }

        if (!replaced)
        {
            if (!AppendEnvVar(env_block, block_size, &cursor, g_Win32Env[i].m_Name, g_Win32Env[i].m_NameLength, g_Win32Env[i].m_Value))
                return false;
        }
    }

    // Loop through our env vars and emit those we didn't already push out.
    for (int i = 0; i < env_count; ++i)
    {
        if (used_env[i])
            continue;
        if (!AppendEnvVar(env_block, block_size, &cursor, env_vars[i].m_Name, env_var_len[i], env_vars[i].m_Value))
            return false;
    }

    env_block[cursor++] = '\0';
    env_block[cursor++] = '\0';
    *out_env_block_length = cursor;
    return true;
}

static int WaitForChildExit(HANDLE processHandle, int (*callback_on_slow)(void *user_data), void *callback_on_slow_userdata)
{
    DWORD waitResult;
    DWORD exitCode;

    DWORD timeout = callback_on_slow == nullptr ? INFINITE : 1000;

    for (;;)
    {
        waitResult = WaitForSingleObject(processHandle, timeout);
        switch (waitResult)
        {
        case WAIT_OBJECT_0:
            // OK - command ran to completion.
            GetExitCodeProcess(processHandle, &exitCode);
            return exitCode;

        case WAIT_TIMEOUT:
            if (callback_on_slow != nullptr)
                (*callback_on_slow)(callback_on_slow_userdata);
            break;

        default:
            CROAK("unhandled WaitForSingleObject result: %d", waitResult);
        }
    }
}

static int WaitForFinish(HANDLE processHandle, int (*callback_on_slow)(void *user_data), void *callback_on_slow_userdata, int time_until_first_callback, std::vector<char> &pipeBuf, HANDLE childPipe)
{
    CHAR buf[PIPE_BUF_SIZE];
    DWORD dwAvail;
    DWORD lastError;

    OVERLAPPED overlapped;
    memset(&overlapped, 0, sizeof(overlapped));
    if (!ReadFile(childPipe, buf, PIPE_BUF_SIZE, nullptr, &overlapped))
    {
        lastError = GetLastError();
        if (lastError == ERROR_BROKEN_PIPE)
            return WaitForChildExit(processHandle, callback_on_slow, callback_on_slow_userdata);

        if (lastError != ERROR_IO_PENDING)
            CROAK("ReadFile returned an unexpected error: %d", lastError);
    }

    DWORD initialTimeout = callback_on_slow == nullptr ? INFINITE : time_until_first_callback;
    DWORD subsequentTimeout = callback_on_slow == nullptr ? INFINITE : 1000;
    DWORD timeout = initialTimeout;

    for (;;)
    {
        if (!GetOverlappedResultEx(childPipe, &overlapped, &dwAvail, timeout, FALSE))
        {
            lastError = GetLastError();
            if (lastError == ERROR_BROKEN_PIPE)
                return WaitForChildExit(processHandle, callback_on_slow, callback_on_slow_userdata);

            if (lastError == WAIT_TIMEOUT)
            {
                if (callback_on_slow != nullptr)
                    (*callback_on_slow)(callback_on_slow_userdata);

                // Note: the previous ReadFile call isn't finished yet.
                // This is why we need the first ReadFile call outside the loop.
                continue;
            }

            CROAK("GetOverlappedResultEx failed: %d", lastError);
        }
        timeout = subsequentTimeout;

        if (dwAvail > 0)
            pipeBuf.insert(pipeBuf.end(), buf, buf+dwAvail);

        // Start another async read.
        memset(&overlapped, 0, sizeof(overlapped));
        if (!ReadFile(childPipe, buf, PIPE_BUF_SIZE, &dwAvail, &overlapped))
        {
            lastError = GetLastError();
            if (lastError == ERROR_BROKEN_PIPE)
                return WaitForChildExit(processHandle, callback_on_slow, callback_on_slow_userdata);

            if (lastError != ERROR_IO_PENDING)
                CROAK("ReadFile returned an unexpected error: %d", lastError);
        }
    }

    return WaitForChildExit(processHandle, callback_on_slow, callback_on_slow_userdata);
}

ExecResult ExecuteProcess(
    const char *cmd_line,
    int env_count,
    const EnvVariable *env_vars,
    MemAllocHeap *heap,
    int job_id,
    bool stream_to_stdout = false,
    int (*callback_on_slow)(void *user_data),
    void *callback_on_slow_userdata,
    int time_until_first_callback)
{
    static uint32_t seq = 0;
    uint32_t sequence_id = AtomicIncrement(&seq);

    char pipe_name[100];
    snprintf(pipe_name, sizeof(pipe_name), "\\\\.\\pipe\\tundra.%u.%d.%u", s_TundraPid, job_id, sequence_id);

    HANDLE pipe = CreateNamedPipeA(pipe_name,
        PIPE_ACCESS_INBOUND | FILE_FLAG_OVERLAPPED, // Open mode.
        PIPE_TYPE_BYTE,                             // Pipe mode.
        1,                                          // Max instances: we don't want other processes opening the pipe.
        0,                                          // Output buffer size: unused with PIPE_ACCESS_INBOUND?
        PIPE_BUF_SIZE,                              // Input buffer size.
        INFINITE,                                   // Default timeout.
        NULL);                                      // Security attributes.
    if (pipe == INVALID_HANDLE_VALUE)
        CROAK("CreateNamedPipeA failed: %d", GetLastError());

    SECURITY_ATTRIBUTES saAttr;
    saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle = TRUE;
    saAttr.lpSecurityDescriptor = NULL;

    // Get the write end of the pipe as a handle inheritable across processes.
    HANDLE child_write_pipe = CreateFileA(pipe_name,
        GENERIC_WRITE, // Desired access.
        0,             // Share mode.
        &saAttr,       // Security attributes which create an inheritable handle.
        OPEN_EXISTING, // Creation disposition.
        0,             // Flags and attributes.
        NULL);         // Template file.
    if (child_write_pipe == INVALID_HANDLE_VALUE)
        CROAK("CreateFileA failed: %d", GetLastError());

    STARTUPINFOEXW sinfo;
    ZeroMemory(&sinfo, sizeof(STARTUPINFOEXW));

    sinfo.StartupInfo.cb = sizeof(STARTUPINFOEXW);
    DWORD creationFlags = CREATE_SUSPENDED | CREATE_UNICODE_ENVIRONMENT;

    bool enherit_handles = !stream_to_stdout;
    void *attributeListAllocation = nullptr;
    if (!stream_to_stdout)
    {
        sinfo.StartupInfo.hStdOutput = sinfo.StartupInfo.hStdError = child_write_pipe;
        sinfo.StartupInfo.hStdInput = GetStdHandle(STD_INPUT_HANDLE);
        sinfo.StartupInfo.dwFlags |= STARTF_USESTDHANDLES;
        creationFlags |= EXTENDED_STARTUPINFO_PRESENT;

        HANDLE handles_to_inherit[2];
        size_t num_handles_to_inherit = 1;
        handles_to_inherit[0] = sinfo.StartupInfo.hStdOutput;

        if (IsWindows8OrGreater()) // Inheriting stdin fails on Windows 7 with Win32 error 1450
        {
            handles_to_inherit[1] = sinfo.StartupInfo.hStdInput;
            ++num_handles_to_inherit;
        }

        SIZE_T attributeListSize = 0;

        //this is pretty crazy, but this call is _supposed_ to fail, and give us the correct attributeListSize, so we verify the returncode !=0
        if (InitializeProcThreadAttributeList(NULL, 1, 0, &attributeListSize))
            CroakErrnoAbort("InitializeProcThreadAttributeList failed");

        attributeListAllocation = HeapAllocate(heap, attributeListSize);
        sinfo.lpAttributeList = static_cast<LPPROC_THREAD_ATTRIBUTE_LIST>(attributeListAllocation);

        //but this call is supposed to succeed, so here we check it for returning ==0
        if (!InitializeProcThreadAttributeList(sinfo.lpAttributeList, 1, 0, &attributeListSize))
            CroakErrno("InitializeProcThreadAttributeList failed (2)");
        if (!UpdateProcThreadAttribute(sinfo.lpAttributeList, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST, handles_to_inherit, sizeof(HANDLE) * num_handles_to_inherit, NULL, NULL))
            CroakErrno("UpdateProcThreadAttribute failed");
    }

    char buffer[8192];
    char env_block[128 * 1024];
    WCHAR env_block_wide[128 * 1024];
    size_t env_block_length = 0;
    if (!MakeEnvBlock(env_block, sizeof(env_block) - 2, env_vars, env_count, &env_block_length))
        CroakAbort("env block error; too big?\n");

    if (!MultiByteToWideChar(CP_UTF8, 0, env_block, (int)env_block_length, env_block_wide, sizeof(env_block_wide) / sizeof(WCHAR)))
        CroakErrnoAbort("Failed converting environment block to wide char");

    ExecResult result;
    char new_cmd[8192];
    ZeroMemory(&result, sizeof(ExecResult));
    ZeroMemory(&new_cmd, sizeof(new_cmd));

    const char *cmd_to_use = new_cmd[0] == 0 ? cmd_line : new_cmd;
    _snprintf(buffer, sizeof(buffer), "cmd.exe /c \"%s\"", cmd_to_use);
    buffer[sizeof(buffer) - 1] = '\0';

    WCHAR buffer_wide[sizeof(buffer) * 2];
    if (!MultiByteToWideChar(CP_UTF8, 0, buffer, (int)sizeof(buffer), buffer_wide, sizeof(buffer_wide) / sizeof(WCHAR)))
        CroakErrnoAbort("Failed converting buffer block to wide char");

    PROCESS_INFORMATION pinfo;

    if (!CreateProcessW(NULL, buffer_wide, NULL, NULL, enherit_handles, creationFlags, env_block_wide, NULL, &sinfo.StartupInfo, &pinfo))
        CroakErrnoAbort("Couldn't launch process");

    if (!stream_to_stdout)
    {
        DeleteProcThreadAttributeList(sinfo.lpAttributeList);
        HeapFree(heap, attributeListAllocation);
    }

    ResumeThread(pinfo.hThread);
    CloseHandle(pinfo.hThread);

    CloseHandle(child_write_pipe); // No longer needed now that the child has been created.

    std::vector<char> pipeBuf;
    pipeBuf.reserve(INITIAL_BUFFER_CAPACITY);
    result.m_ReturnCode = WaitForFinish(pinfo.hProcess,
        callback_on_slow, callback_on_slow_userdata, time_until_first_callback,
        pipeBuf, pipe);

    CloseHandle(pipe);

    if (!stream_to_stdout)
        CopyOutputIntoBuffer(job_id, buffer, &result.m_OutputBuffer, heap, pipeBuf);

    CloseHandle(pinfo.hProcess);

    return result;
}



#endif /* TUNDRA_WIN32 */
