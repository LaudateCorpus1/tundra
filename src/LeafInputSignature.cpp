#include "LeafInputSignature.hpp"
#include "Hash.hpp"
#include "DagData.hpp"
#include "RuntimeNode.hpp"
#include "BuildQueue.hpp"
#include "Profiler.hpp"
#include "FileSign.hpp"
#include "Scanner.hpp"
#include "Driver.hpp"
#include "Exec.hpp"
#include "NodeResultPrinting.hpp"
#include "AllBuiltNodes.hpp"
#include <time.h>

static bool FilterOutGeneratedIncludedFiles(void* _userData, const char* includingFile, const char* includedFile)
{
    //return true if we want to process the file, false if we want it to be skipped
    return !IsFileGenerated((DagRuntimeData*)_userData, Djb2HashPath(includedFile), includedFile);
}

static HashDigest CalculateLeafInputSignatureHot(const int32_t* dagNodeIndexToRuntimeNodeIndex_Table,
    RuntimeNode* runtimeNodesArray,
    const Frozen::Dag* dag,
    const Frozen::DagDerived* dagDerived,
    const DagRuntimeData *dagRuntime,
    const Frozen::DagNode* dagNode,
    RuntimeNode* runtimeNode,
    MemAllocHeap* heap,
    MemAllocLinear* scratch,
    int profilerThreadId,
    StatCache* stat_cache,
    DigestCache* digest_cache,
    ScanCache* scan_cache,
    FILE* ingredient_stream)
{
    HashState hashState;
    HashInit(&hashState);

    for (auto& child: dagDerived->m_DependentNodesThatThemselvesAreLeafInputCacheable[dagNode->m_DagNodeIndex])
    {
        int childRuntimeNodeIndex = dagNodeIndexToRuntimeNodeIndex_Table[child];
        auto& childRuntimeNode = runtimeNodesArray[childRuntimeNodeIndex];
        const auto& childDagNode = dag->m_DagNodes[child];

        if (childRuntimeNode.m_CurrentLeafInputSignature.m_Words64[0] == 0)
        {
            //this is racy, but it should be okay(tm). It's possible the leaf input signature isn't stored yet, but another thread is already calculating it.
            //in that case we calculate it too, and both threads will just store the same value.
            childRuntimeNode.m_CurrentLeafInputSignature = CalculateLeafInputSignatureHot(dagNodeIndexToRuntimeNodeIndex_Table, runtimeNodesArray, dag, dagDerived, dagRuntime, &childDagNode, &childRuntimeNode, heap, scratch, profilerThreadId, stat_cache, digest_cache, scan_cache, nullptr);
        }

        if (ingredient_stream)
        {
            char childLeafInputSignatureStr[kDigestStringSize];
            DigestToString(childLeafInputSignatureStr, childRuntimeNode.m_CurrentLeafInputSignature);
            fprintf(ingredient_stream, "cacheabledependentnode: %s %s\n", childLeafInputSignatureStr, childDagNode.m_Annotation.Get());
        }
        HashUpdate(&hashState, &childRuntimeNode.m_CurrentLeafInputSignature, sizeof(HashDigest));
    }

    //starting the profiler scope late here, because we do not support nested profiler scope, and at the top of this function we recurse.
    ProfilerScope profiler_scope("ComputeLeafInputSignature", profilerThreadId, dagNode->m_Annotation);

    HashUpdate(&hashState, &(dagDerived->m_LeafInputHash_Offline[dagNode->m_DagNodeIndex]), sizeof(HashDigest));

    const FrozenArray<FrozenFileAndHash>& leafInputs = dagDerived->m_NodeLeafInputs[dagNode->m_DagNodeIndex];

    HashSet<kFlagPathStrings> localExplicitLeafInputs;
    HashSet<kFlagPathStrings> localImplicitLeafInputs;

    auto& explicitLeafInputs = runtimeNode == nullptr ? localExplicitLeafInputs : runtimeNode->m_ExplicitLeafInputs;
    auto& implicitLeafInputs = runtimeNode == nullptr ? localImplicitLeafInputs : runtimeNode->m_ImplicitLeafInputs;

    HashSetInit(&explicitLeafInputs, heap);
    HashSetInit(&implicitLeafInputs, heap);
    for (auto& leafInput: leafInputs)
        HashSetInsert(&explicitLeafInputs, leafInput.m_FilenameHash, leafInput.m_Filename.Get());

    ScanInput scanInput;
    scanInput.m_SafeToScanBeforeDependenciesAreProduced = true;
    scanInput.m_ScanCache = scan_cache;
    scanInput.m_ScratchAlloc = scratch;
    scanInput.m_ScratchHeap = heap;

    MemAllocLinear scanResults;
    LinearAllocInit(&scanResults, heap, MB(4), "ComputeLeafInputSignature");

    IncludeFilterCallback ignoreCallback;
    ignoreCallback.userData = (void*)dagRuntime;
    ignoreCallback.callback = FilterOutGeneratedIncludedFiles;

    for (const Frozen::ScannerIndexWithListOfFiles& scannerIndexWithListOfFiles : dagDerived->m_Nodes_to_ScannersWithListsOfFiles[dagNode->m_DagNodeIndex])
    {
        scanInput.m_ScannerConfig = dag->m_Scanners[scannerIndexWithListOfFiles.m_ScannerIndex];

        for (const FrozenFileAndHash& file: scannerIndexWithListOfFiles.m_FilesToScan)
        {
            MemAllocLinearScope allocScope(scratch);
            scanInput.m_FileName = file.m_Filename;

            ScanOutput scanOutput;
            if (ScanImplicitDeps(stat_cache, &scanInput, &scanOutput, &ignoreCallback))
            {
                for(int i=0; i < scanOutput.m_IncludedFileCount; i++)
                {
                    const FileAndHash& includedFile = scanOutput.m_IncludedFiles[i];
                    if (HashSetLookup(&explicitLeafInputs, includedFile.m_FilenameHash, includedFile.m_Filename))
                        continue;
                    if (HashSetLookup(&implicitLeafInputs, includedFile.m_FilenameHash, includedFile.m_Filename))
                        continue;
                    HashSetInsert(&implicitLeafInputs, includedFile.m_FilenameHash,/*todo: free this memory*/ StrDup(heap, includedFile.m_Filename));
                }
            }
        }
    }

    auto addFileContentsToHash = [&](const char* filename, uint32_t filename_hash, const char* label)
    {
        HashDigest digest = ComputeFileSignatureSha1(stat_cache, digest_cache, filename, filename_hash);

        if (ingredient_stream)
        {
            char digestString[kDigestStringSize];
            DigestToString(digestString, digest);
            char buffer[kMaxPathLength];
            strncpy(buffer, filename, sizeof(buffer));
            char*p = buffer;
            for ( ; *p; ++p) *p = tolower(*p);
            fprintf(ingredient_stream, "%s: %s %s\n", label, digestString, buffer);
        }
        HashAddPath(&hashState, filename);
        HashUpdate(&hashState, &digest, sizeof(digest));
    };

    HashSetWalk(&explicitLeafInputs, [&](uint32_t index, uint32_t hash, const char *filename) {
        addFileContentsToHash(filename, hash, "explicitLeafInput");
    });
    HashSetWalk(&implicitLeafInputs, [&](uint32_t index, uint32_t hash, const char *filename) {
        addFileContentsToHash(filename, hash, "implicitLeafInput");
    });

    HashDigest result;
    HashFinalize(&hashState, &result);

    LinearAllocDestroy(&scanResults);

    return result;
}

//This function calculates the offline part of the signature, which we store in the dag-derived file
HashDigest CalculateLeafInputHashOffline(const Frozen::Dag* dag, std::function<const int32_t*(int)>& arrayAccess, std::function<size_t(int)>& sizeAccess, int32_t nodeIndex, MemAllocHeap* heap, FILE* ingredient_stream)
{
    HashDigest hashResult = {};

    Buffer<int32_t> all_dependent_nodes;
    BufferInit(&all_dependent_nodes);

    std::function<bool(int,int)> filterLeafInputCacheable = [&](int parentIndex, int childIndex)
    {
        bool isCacheable = dag->m_DagNodes[childIndex].m_Flags & Frozen::DagNode::kFlagCacheableByLeafInputs;
        return !isCacheable;
    };
    FindDependentNodesFromRootIndex(heap, dag, arrayAccess, sizeAccess, filterLeafInputCacheable, nodeIndex, all_dependent_nodes);

    HashState hashState;
    HashInit(&hashState);

    std::sort(all_dependent_nodes.begin(), all_dependent_nodes.end(), [dag](const int& a, const int& b) { return strcmp(dag->m_DagNodes[a].m_Annotation.Get(), dag->m_DagNodes[b].m_Annotation.Get()) < 0; });

    for(int32_t childNodeIndex : all_dependent_nodes)
    {
        auto& dagNode = dag->m_DagNodes[childNodeIndex];

        if (ingredient_stream)
            fprintf(ingredient_stream, "\nannotation: %s\n", dagNode.m_Annotation.Get());

        HashAddString(ingredient_stream, &hashState, "action", dagNode.m_Action.Get());

        for(auto& env: dagNode.m_EnvVars)
        {
            HashAddString(ingredient_stream, &hashState, "env_name", env.m_Name);
            HashAddString(ingredient_stream, &hashState, "env_value", env.m_Value);
        }
        for (auto& s: dagNode.m_AllowedOutputSubstrings)
            HashAddString(ingredient_stream, &hashState, "allowed_outputstring", s);
        for (auto& f: dagNode.m_OutputFiles)
            HashAddString(ingredient_stream, &hashState, "output", f.m_Filename.Get());

        int relevantFlags = dagNode.m_Flags & ~Frozen::DagNode::kFlagCacheableByLeafInputs;

        //if our flags are completely default, let's not add them to the stream, it makes the ingredient stream easier
        //to parse/compare for a human.
        if (relevantFlags != (Frozen::DagNode::kFlagOverwriteOutputs | Frozen::DagNode::kFlagAllowUnexpectedOutput))
            HashAddInteger(ingredient_stream, &hashState, "flags", relevantFlags);
    }
    HashFinalize(&hashState, &hashResult);

    BufferDestroy(&all_dependent_nodes, heap);
    return hashResult;
};


HashDigest CalculateLeafInputSignature(BuildQueue* queue, ThreadState* thread_state, RuntimeNode* node)
{
    char path[kMaxPathLength];
    snprintf(path, sizeof(path), "%s/tmp-%d", queue->m_Config.m_Dag->m_CacheSignatureDirectoryName.Get(), node->m_DagNodeIndex);

    char offlinePath[kMaxPathLength];
    snprintf(offlinePath, sizeof(offlinePath), "%s/offline-%d", queue->m_Config.m_Dag->m_CacheSignatureDirectoryName.Get(), node->m_DagNodeIndex);

    FILE *sig = fopen(path, "w");
    FILE *sigoffline = fopen(offlinePath, "r");

    if (sig == NULL)
        CroakErrno("Failed opening signature ingredients for writing.");

#if TUNDRA_WIN32
    const char* username = getenv("USERNAME");
    if (username != nullptr)
        fprintf(sig, "Signature generated by %s\n", username);
#else
    char hostname[1024];
    if (gethostname(hostname, sizeof(hostname)) == 0)
        fprintf(sig, "Signature generated by %s\n", hostname);
#endif
    time_t rawtime;
    struct tm *info;
    time( &rawtime );
    info = localtime( &rawtime );
    fprintf(sig, "Current local time and date: %s", asctime(info));
    fprintf(sig, "Annotation %s\n\n", node->m_DagNode->m_Annotation.Get());

    if (sigoffline != nullptr)
    {
        fprintf(sig, "Cold hash ingredients (anything below this line is hashed and must not change to get a cache hit):\n");

        char            buffer[1024];
        size_t          n;

        while ((n = fread(buffer, sizeof(char), sizeof(buffer), sigoffline)) > 0)
        {
            if (fwrite(buffer, sizeof(char), n, sig) != n)
                CroakErrno("Failed writing cold signature ingredients.");
        }
        fclose(sigoffline);
    }

    fprintf(sig, "Hot hash ingredients:\n");
    HashDigest res = CalculateLeafInputSignatureHot(
            queue->m_Config.m_DagNodeIndexToRuntimeNodeIndex_Table,
            queue->m_Config.m_RuntimeNodes,
            queue->m_Config.m_Dag,
            queue->m_Config.m_DagDerived,
            &queue->m_Config.m_DagRuntimeData,
            node->m_DagNode,
            node,
            &thread_state->m_LocalHeap,
            &thread_state->m_ScratchAlloc,
            thread_state->m_ProfilerThreadId,
            queue->m_Config.m_StatCache,
            queue->m_Config.m_DigestCache,
            queue->m_Config.m_ScanCache,
            sig);
    fclose(sig);

    char digestString[kDigestStringSize];
    DigestToString(digestString, res);

    char new_path[kMaxPathLength];
    snprintf(new_path, sizeof(path), "%s/%s", queue->m_Config.m_Dag->m_CacheSignatureDirectoryName.Get(), digestString);
    if (!RenameFile(path, new_path))
        CroakErrno("Failed moving signature ingredients file.");

    return res;
}

void PrintLeafInputSignature(Driver* driver, const char **argv, int argc)
{
    Buffer<int32_t> requestedNodes;
    BufferInit(&requestedNodes);
    const Frozen::Dag* dag = driver->m_DagData;

    DriverSelectNodes(dag, argv, argc, &requestedNodes, &driver->m_Heap);
    if (requestedNodes.m_Size == 0)
        Croak("Cannot find requested target");
    if (requestedNodes.m_Size > 1)
        Croak("You can only print the leaf input signature for a single node, but %d are requested", requestedNodes.m_Size);

    int32_t requestedNode = requestedNodes[0];
    const Frozen::DagNode& dagNode = dag->m_DagNodes[requestedNode];

    if (0 == (dagNode.m_Flags & Frozen::DagNode::kFlagCacheableByLeafInputs))
    {
        Croak("Requested node %s is not cacheable by leaf inputs\n", dagNode.m_Annotation.Get());
    }

    printf("OffLine ingredients to the leaf input hash\n");
    std::function<const int32_t*(int)> arrayAccess = [=](int index){return driver->m_DagDerivedData->m_Dependencies[index].GetArray();};
    std::function<size_t(int)> sizeAccess = [=](int index){return driver->m_DagDerivedData->m_Dependencies[index].GetCount();};
    CalculateLeafInputHashOffline(dag, arrayAccess, sizeAccess, requestedNode, &driver->m_Heap, stdout);

    printf("\n\n\nRuntime ingredients to the leaf input hash\n");
    MemAllocLinear scratch;
    LinearAllocInit(&scratch, &driver->m_Heap, MB(16), "PrintLeafInputSignature");
    DagRuntimeData runtimeData;
    DagRuntimeDataInit(&runtimeData, driver->m_DagData, &driver->m_Heap);

    CalculateLeafInputSignatureHot(
        driver->m_DagNodeIndexToRuntimeNodeIndex_Table.begin(),
        driver->m_RuntimeNodes.begin(),
        driver->m_DagData,
        driver->m_DagDerivedData,
        &runtimeData,
        &dagNode,
        nullptr,
        &driver->m_Heap,
        &scratch,
        0,
        &driver->m_StatCache,
        &driver->m_DigestCache,
        &driver->m_ScanCache,
        stdout);

    DagRuntimeDataDestroy(&runtimeData);
    LinearAllocDestroy(&scratch);
}



#define PRINT_ALL_MISSING_FILES 0

bool VerifyAllVersionedFilesIncludedByGeneratedHeaderFilesWereAlreadyPartOfTheLeafInputs(BuildQueue* queue, ThreadState* thread_state, RuntimeNode* node, const Frozen::DagDerived* dagDerived)
{
#if PRINT_ALL_MISSING_FILES
    bool fail = false;
#endif
    for(auto nodeWithScanner: dagDerived->m_RecursiveDependenciesWithScanners[node->m_DagNodeIndex])
    {
        int runtimeNodeIndex = queue->m_Config.m_DagNodeIndexToRuntimeNodeIndex_Table[nodeWithScanner];

        //find runtimenode:
        RuntimeNode* runtimeNodeWithScanner = &queue->m_Config.m_RuntimeNodes[runtimeNodeIndex];

        auto IsAlreadyLeafInput = [=](uint32_t hash, const char* filename) -> bool
        {
            if (HashSetLookup(&node->m_ExplicitLeafInputs, hash,filename))
                return true;
            if (HashSetLookup(&node->m_ImplicitLeafInputs, hash,filename))
                return true;
            return false;
        };

        auto PrintHeaderError = [=](const char* includedFile, const char* includingFile)
        {
            ExecResult result = {0, false};
            result.m_ReturnCode = 1;

            InitOutputBuffer(&result.m_OutputBuffer, &thread_state->m_LocalHeap);

            const char* formatString =
            "This node '%s' is marked as leaf input cacheable.\n"
            "It has a dependency node '%s' whose inputfile is being scanned for includes.\n"
            "Generated file '%s' was found including the non generated file '%s'.\n"
            "Because '%s' is exclusively included by generated files,\n"
            "this node cannot be safely cached.\n"
            "You can fix this by either:\n"
            "- Making '%s' not include '%s'.\n"
            "- By ensuring that this build has a non-generated file that also includes '%s'.\n"
            "- By using the filesThatMightBeIncluded feature.\n";

            char buffer[4096];
            snprintf(buffer,sizeof(buffer), formatString,
                node->m_DagNode->m_Annotation.Get(),
                runtimeNodeWithScanner->m_DagNode->m_Annotation.Get(),
                includingFile,
                includedFile,
                includedFile,
                includingFile,
                includedFile,
                includedFile
            );

            result.m_FrozenNodeData = node->m_DagNode;
            EmitOutputBytesToDestination(&result, buffer, strlen(buffer));

            MutexLock(&queue->m_Lock);
            PrintNodeResult(&result, node->m_DagNode, "No command was run. Files were scanned for includes in preparation of running.", queue, thread_state, false, TimerGet(), ValidationResult::Pass, nullptr, true);
            MutexUnlock(&queue->m_Lock);

            ExecResultFreeMemory(&result);
        };

        switch (runtimeNodeWithScanner->m_BuildResult)
        {
            case NodeBuildResult::kUpToDate:

                for(const Frozen::IncludingIncludedPair& pair: runtimeNodeWithScanner->m_BuiltNode->m_VersionedFilesIncludedByGeneratedFiles)
                {
                    if (!IsAlreadyLeafInput(pair.m_IncludedFile.m_FilenameHash, pair.m_IncludedFile.m_Filename.Get()))
                    {
#if !PRINT_ALL_MISSING_FILES
                        PrintHeaderError(pair.m_IncludedFile.m_Filename.Get(), pair.m_IncludingFile.Get());
                        return false;
#else
                        printf("#include \"%s\"\n", pair.m_IncludedFile.m_Filename.Get());
                        fail=true;
#endif
                    }
                }

                break;
            case NodeBuildResult::kRanSuccesfully:
                for(auto pair: runtimeNodeWithScanner->m_GeneratedFilesIncludingVersionedFiles)
                {
                    if (!IsAlreadyLeafInput(Djb2HashPath(pair.m_IncludedFile), pair.m_IncludedFile))
                    {
#if !PRINT_ALL_MISSING_FILES
                        PrintHeaderError(pair.m_IncludedFile, pair.m_IncludingFile);
                        return false;
#else
                        printf("#include \"%s\"\n", pair.m_IncludedFile);
                        fail = true;
#endif
                    }
                }

                break;
            default:
                Croak("Unexpected build node result of dependent node while verifying headers");
        }


    }
#if PRINT_ALL_MISSING_FILES
    if (fail)
            return false;
#endif
    return true;
}
