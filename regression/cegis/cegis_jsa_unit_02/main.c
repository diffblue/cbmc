#ifdef __CPROVER
#define __CPROVER_JSA_MAX_CONCRETE_NODES 2u
#define __CPROVER_JSA_MAX_ABSTRACT_NODES 0u
#define __CPROVER_JSA_MAX_ITERATORS 2u
#define __CPROVER_JSA_MAX_LISTS 2u

#define JSA_SYNTHESIS_H_
#define __CPROVER_JSA_DEFINE_TRANSFORMERS
#define __CPROVER_JSA_MAX_QUERY_SIZE 2u
#define __CPROVER_JSA_MAX_PRED_SIZE 1u
#define __CPROVER_JSA_NUM_PRED_OPS 3u
#define __CPROVER_JSA_NUM_PRED_RESULT_OPS 2u
#endif

#include "../../../src/ansi-c/library/jsa.h"

#include <stdio.h>

int main(void)
{
  __CPROVER_jsa_abstract_heapt heap;
  __CPROVER_jsa_assume_valid_heap(&heap);
  const __CPROVER_jsa_list_id_t __CPROVER_jsa_list_list=0;
  __CPROVER_jsa_assume_valid_list(&heap, __CPROVER_jsa_list_list);
  const __CPROVER_jsa_list_id_t __CPROVER_jsa_list_nonZero=1;
  __CPROVER_jsa_assume_new_list(&heap, __CPROVER_jsa_list_nonZero);
  const __CPROVER_jsa_iterator_id_t __CPROVER_jsa_iterator_it=__CPROVER_jsa_iterator(&heap, __CPROVER_jsa_list_list);
  __CPROVER_jsa_assume(__CPROVER_jsa_hasNext(&heap, __CPROVER_jsa_iterator_it));

  const __CPROVER_jsa_data_t tmp=__CPROVER_jsa_next(&heap, __CPROVER_jsa_iterator_it);
  __CPROVER_jsa_add(&heap, __CPROVER_jsa_list_nonZero, tmp);
  __CPORVER_assert(!__CPROVER_jsa_hasNext(&heap, __CPROVER_jsa_iterator_it));
  const __CPROVER_jsa_iterator_id_t __CPROVER_jsa_iterator_copy_it=__CPROVER_jsa_iterator(&heap, __CPROVER_jsa_list_nonZero);
  const __CPROVER_jsa_data_t tmp2=__CPROVER_jsa_next(&heap, __CPROVER_jsa_iterator_copy_it);
  __CPROVER_jsa_assume(tmp == tmp2);

  __CPROVER_assert(0 == 1, "");

  return 0;
}
