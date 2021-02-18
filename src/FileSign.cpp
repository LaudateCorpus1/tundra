#include "FileSign.hpp"
#include "Hash.hpp"
#include "StatCache.hpp"
#include "Stats.hpp"
#include "DigestCache.hpp"
#include "Buffer.hpp"
#include <stdio.h>


HashDigest ComputeFileSignatureSha1(StatCache* stat_cache, DigestCache* digest_cache, const char* filename, uint32_t fn_hash)
{
    HashDigest result = {};

    FileInfo file_info = StatCacheStat(stat_cache, filename, fn_hash);

    if (!file_info.Exists())
    {
        return result;
    }

    if (!DigestCacheGet(digest_cache, filename, fn_hash, file_info.m_Timestamp, &result))
    {
        TimingScope timing_scope(&g_Stats.m_FileDigestCount, &g_Stats.m_FileDigestTimeCycles);

        FILE *f = fopen(filename, "rb");
        if (!f)
            return result;

        HashState h;
        HashInit(&h);

        char buffer[8192];
        while (size_t nbytes = fread(buffer, 1, sizeof buffer, f))
        {
            HashUpdate(&h, buffer, nbytes);
        }
        fclose(f);

        HashFinalize(&h, &result);
        DigestCacheSet(digest_cache, filename, fn_hash, file_info.m_Timestamp, result);
    }
    else
    {
        AtomicIncrement(&g_Stats.m_DigestCacheHits);
    }
    return result;
}

void ComputeFileSignatureSha1(HashState *state, StatCache *stat_cache, DigestCache *digest_cache, const char *filename, uint32_t fn_hash)
{
    HashDigest digest = ComputeFileSignatureSha1(stat_cache, digest_cache, filename, fn_hash);
    HashUpdate(state, &digest, sizeof(digest));
}

bool ShouldUseSHA1SignatureFor(const char *filename, const uint32_t sha_extension_hashes[], int sha_extension_hash_count)
{
    const char *ext = strrchr(filename, '.');
    if (!ext)
        return false;

    uint32_t ext_hash = Djb2Hash(ext);
    for (int i = 0; i < sha_extension_hash_count; ++i)
    {
        if (sha_extension_hashes[i] == ext_hash)
            return true;
    }

    return false;
}

HashDigest CalculateGlobSignatureFor(const char *path, const char *filter, bool recurse, MemAllocHeap *heap, MemAllocLinear *scratch)
{
    // Helper for directory iteration + memory allocation of strings.  We need to
    // buffer the filenames as we need them in sorted order to ensure the results
    // are consistent between runs.
    struct IterContext
    {
        MemAllocLinear *m_Allocator;
        MemAllocHeap *m_Heap;
        Buffer<const char *> m_Dirs;
        Buffer<const char *> m_Files;

        void Init(MemAllocHeap *heap, MemAllocLinear *linear)
        {
            m_Allocator = linear;
            m_Heap = heap;
            BufferInit(&m_Dirs);
            BufferInit(&m_Files);
        }

        void Destroy()
        {
            BufferDestroy(&m_Files, m_Heap);
            BufferDestroy(&m_Dirs, m_Heap);
        }

        static void Callback(void *user_data, const FileInfo &info, const char *path)
        {
            IterContext *self = (IterContext *)user_data;
            char *data = StrDup(self->m_Allocator, path);
            Buffer<const char *> *target = info.IsDirectory() ? &self->m_Dirs : &self->m_Files;
            BufferAppendOne(target, self->m_Heap, data);
        }

        static int SortStringPtrs(const void *l, const void *r)
        {
            return strcmp(*(const char **)l, *(const char **)r);
        }
    };

    HashState h;
    HashInit(&h);

    FileInfo pathInfo = GetFileInfo(path);
    HashAddInteger(&h, pathInfo.Exists() ? 1 : 0);
    HashAddInteger(&h, pathInfo.IsDirectory() ? 1 : 0);
    HashAddSeparator(&h);

    if (pathInfo.Exists() && pathInfo.IsDirectory())
    {
        // Set up to rewind allocator for each loop iteration
        MemAllocLinearScope mem_scope(scratch);

        // Set up context
        IterContext ctx;
        ctx.Init(heap, scratch);

        // Get directory data
        ListDirectory(path, filter, recurse, &ctx, IterContext::Callback);

        // Sort data
        qsort(ctx.m_Dirs.m_Storage, ctx.m_Dirs.m_Size, sizeof(const char *), IterContext::SortStringPtrs);
        qsort(ctx.m_Files.m_Storage, ctx.m_Files.m_Size, sizeof(const char *), IterContext::SortStringPtrs);

        // Compute digest
        for (const char *p : ctx.m_Dirs)
        {
            HashAddPath(&h, p);
            HashAddSeparator(&h);
        }

        // Add an extra separator to catch a directory that turned into a file
        HashAddSeparator(&h);

        for (const char *p : ctx.m_Files)
        {
            HashAddPath(&h, p);
            HashAddSeparator(&h);
        }

        ctx.Destroy();
    }
    else if (pathInfo.IsFile())
    {
        HashAddInteger(&h, pathInfo.m_Timestamp);
    }

    HashDigest digest;
    HashFinalize(&h, &digest);

    return digest;
}


