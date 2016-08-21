
#ifdef __CPROVER
#define __CPROVER_JSA_MAX_CONCRETE_NODES 1u
#define __CPROVER_JSA_MAX_ABSTRACT_NODES 0u
#define __CPROVER_JSA_MAX_ITERATORS 1u
#define __CPROVER_JSA_MAX_LISTS 1u

#define JSA_SYNTHESIS_H_
#define __CPROVER_JSA_DEFINE_TRANSFORMERS
#define __CPROVER_JSA_MAX_QUERY_SIZE 2u
#define __CPROVER_JSA_MAX_PRED_SIZE 1u
#endif

#include "../../../src/ansi-c/library/jsa.h"

__CPROVER_jsa_abstract_heapt nondet_heap(void);

int main(void)
{
  __CPROVER_jsa_abstract_heapt heap=
  {
    .concrete_nodes={ { .next=255, .previous=255, .list=0, .value=16 } },
    .abstract_nodes=((struct __CPROVER_jsa_abstract_node *)0),
    .abstract_ranges=((struct __CPROVER_jsa_abstract_range *)0),
    .iterators={ { .node_id=255, .previous_node_id=255, .index=0, .previous_index=0, .list=255 } },
    .iterator_count=0,
    .list_head_nodes={ 0 },
    .list_count=1
  };
  __CPROVER_jsa_assume_valid_heap(&heap);
  const __CPROVER_jsa_list_id_t __CPROVER_jsa_list_list;
  __CPROVER_jsa_assume_valid_list(&heap, __CPROVER_jsa_list_list);
  const __CPROVER_jsa_data_t limit=3;
  __CPROVER_jsa_iterator_id_t __CPROVER_jsa_iterator_it=__CPROVER_jsa_iterator(&heap, __CPROVER_jsa_list_list);

  unsigned char pred_size=1;
  __CPROVER_jsa_pred_instructiont __CPROVER_jsa_predicate[] = { { .opcode=0, .result_op=0, .op0=1, .op1=0 } };
  __CPROVER_JSA_PREDICATES[0]=__CPROVER_jsa_predicate;
  __CPROVER_JSA_PREDICATE_SIZES[0]=pred_size;
  unsigned char lambda_op=0;
  unsigned char tmp0=0;
  unsigned char tmp1=0;
  unsigned char tmp2=0;
  __CPROVER_JSA_PRED_OPS[0]=&lambda_op;
  __CPROVER_JSA_PRED_OPS[1]=&limit;
  __CPROVER_JSA_PRED_RESULT_OPS[0]=&tmp0;
  __CPROVER_JSA_PRED_RESULT_OPS[1]=&tmp1;
  __CPROVER_JSA_PRED_RESULT_OPS[2]=&tmp2;
  unsigned char query_size=2;
  __CPROVER_assume(query_size >= 1 && query_size <= __CPROVER_JSA_MAX_QUERY_SIZE);
  __CPROVER_jsa_query_instructiont __CPROVER_jsa_query[] = { { .opcode=0, .op0=0, .op1=0 }, { .opcode=0, .op0=0, .op1=__CPROVER_jsa_null } };
  unsigned char invariant_size;
  __CPROVER_assume(invariant_size >= 1 && invariant_size <= 1);
  __CPROVER_jsa_invariant_instructiont invariant[] = { { .opcode=0 } };
  __CPROVER_jsa_abstract_heapt queried_heap=heap;
  __CPROVER_jsa_query_execute(&queried_heap, __CPROVER_jsa_query, query_size);
  _Bool base_case=__CPROVER_jsa_invariant_execute(&heap, &queried_heap, invariant, invariant_size);
  __CPROVER_assume(base_case);

  const __CPROVER_jsa_abstract_heapt __tmp=
  {
    .concrete_nodes={ { .next=255, .previous=255, .list=0, .value=16 } },
    .abstract_nodes=((struct __CPROVER_jsa_abstract_node *)0),
    .abstract_ranges=((struct __CPROVER_jsa_abstract_range *)0),
    .iterators={ { .node_id=0, .previous_node_id=255, .index=0, .previous_index=0, .list=0 } },
    .iterator_count=1,
    .list_head_nodes={ 0 },
    .list_count=1
  };
  heap=__tmp;
  __CPROVER_jsa_abstract_heapt org_heap = heap;
  queried_heap=org_heap;
  __CPROVER_jsa_query_execute(&queried_heap, __CPROVER_jsa_query, query_size);
  _Bool invariant_assume=__CPROVER_jsa_invariant_execute(&heap, &queried_heap, invariant, invariant_size);
  __CPROVER_assume(invariant_assume);

  //while (__CPROVER_jsa_hasNext(&heap, __CPROVER_jsa_iterator_it))
  if (__CPROVER_jsa_hasNext(&heap, __CPROVER_jsa_iterator_it))
  {
    const __CPROVER_jsa_data_t value=__CPROVER_jsa_next(&heap, __CPROVER_jsa_iterator_it);
    if (value <= limit)
    {
      __CPROVER_jsa_remove(&heap, __CPROVER_jsa_iterator_it);
    }

    queried_heap=org_heap;
    __CPROVER_jsa_synchronise_iterator(&heap, &queried_heap, __CPROVER_jsa_query, query_size);
    __CPROVER_jsa_query_execute(&queried_heap, __CPROVER_jsa_query, query_size);
    _Bool invariant_step=__CPROVER_jsa_invariant_execute(&heap, &queried_heap, invariant, invariant_size);
    __CPROVER_assume(invariant_step);
  }
  else
  {
    queried_heap=org_heap;
    __CPROVER_jsa_full_query_execute(&queried_heap, __CPROVER_jsa_query, query_size);
    _Bool property_entailment=__CPROVER_jsa_invariant_execute(&org_heap, &queried_heap, invariant, invariant_size);
    __CPROVER_assume(invariant_assume);
  }

  __CPROVER_assert(0 == 1, "");
  return 0;
}
