#include "DagData.hpp"
#include "Buffer.hpp"

void FindDependentNodesFromRootIndices(MemAllocHeap* heap, const Frozen::Dag* dag, int32_t* searchRootIndices, int32_t searchRootCount, Buffer<int32_t>& results)
{
    Buffer<int32_t> node_stack;
    BufferInitWithCapacity(&node_stack, heap, 1024);
    BufferAppend(&node_stack, heap, searchRootIndices, searchRootCount);

    int node_count = 0;
    const Frozen::DagNode *src_nodes = dag->m_DagNodes;

    const size_t node_word_count = (dag->m_NodeCount + 31) / 32;
    uint32_t *node_visited_bits = HeapAllocateArrayZeroed<uint32_t>(heap, node_word_count);

    while (node_stack.m_Size > 0)
    {
        int dag_index = BufferPopOne(&node_stack);
        const int dag_word = dag_index / 32;
        const int dag_bit = 1 << (dag_index & 31);

        if (0 == (node_visited_bits[dag_word] & dag_bit))
        {
            const Frozen::DagNode *node = src_nodes + dag_index;

            BufferAppendOne(&results, heap, dag_index);

            node_visited_bits[dag_word] |= dag_bit;

            // Update counts
            ++node_count;

            // Stash node dependencies on the work queue to keep iterating
            BufferAppend(&node_stack, heap, node->m_Dependencies.GetArray(), node->m_Dependencies.GetCount());
        }
    }

    HeapFree(heap, node_visited_bits);
    node_visited_bits = nullptr;
}
