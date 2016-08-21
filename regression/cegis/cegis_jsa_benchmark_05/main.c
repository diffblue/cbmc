
#ifdef __CPROVER
#define __CPROVER_JSA_MAX_CONCRETE_NODES 1u
#define __CPROVER_JSA_MAX_ABSTRACT_NODES 0u
#define __CPROVER_JSA_MAX_ITERATORS 1u
#define __CPROVER_JSA_MAX_LISTS 1u
#endif

#include "../../../src/ansi-c/library/jsa.h"

int main(void)
{
  __CPROVER_jsa_abstract_heapt heap;
  __CPROVER_jsa_assume_valid_heap(&heap);
  const __CPROVER_jsa_list_id_t __CPROVER_jsa_list_list;
  __CPROVER_jsa_assume_valid_list(&heap, __CPROVER_jsa_list_list);
  __CPROVER_jsa_data_t max=0;
  for (const __CPROVER_jsa_iterator_id_t __CPROVER_jsa_iterator_it=__CPROVER_jsa_iterator(&heap, __CPROVER_jsa_list_list);
       __CPROVER_jsa_hasNext(&heap, __CPROVER_jsa_iterator_it);)
  {
    const __CPROVER_jsa_data_t v=__CPROVER_jsa_next(&heap, __CPROVER_jsa_iterator_it);
    if (v > max)
    {
      max = v;
    }
  }

  return 0;
}
