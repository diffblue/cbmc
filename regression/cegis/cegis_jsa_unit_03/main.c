#ifdef __CPROVER
#define __CPROVER_JSA_MAX_CONCRETE_NODES 2u
#define __CPROVER_JSA_MAX_ABSTRACT_NODES 0u
#define __CPROVER_JSA_MAX_ITERATORS 1u
#define __CPROVER_JSA_MAX_LISTS 2u

#define JSA_SYNTHESIS_H_
#define __CPROVER_JSA_DEFINE_TRANSFORMERS
#define __CPROVER_JSA_MAX_QUERY_SIZE 2u
#define __CPROVER_JSA_MAX_PRED_SIZE 1u
#define __CPROVER_JSA_NUM_PRED_OPS 3u
#define __CPROVER_JSA_NUM_PRED_RESULT_OPS 2u
#endif

#include "../../../src/ansi-c/library/jsa.h"

#define NULL 0

int main(void)
{
  const __CPROVER_jsa_abstract_heapt heap={ .concrete_nodes={ { .next=255, .previous=255, .list=255, .value=255 },
      { .next=255, .previous=255, .list=255, .value=255 } }, .abstract_nodes=((struct __CPROVER_jsa_abstract_node *)NULL),
      .abstract_ranges=((struct __CPROVER_jsa_abstract_range *)NULL),
      .iterators={ { .node_id=255, .previous_node_id=255, .index=0, .previous_index=0,
      .list=0 } },
      .iterator_count=1,
      .list_head_nodes={ 255, 255 }, .list_count=2 };
  __CPROVER_jsa_assume_valid_heap(&heap);

  __CPROVER_assert(0 == 1, "");
  return 0;
}
