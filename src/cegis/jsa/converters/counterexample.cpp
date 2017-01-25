/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/bv_arithmetic.h>
#include <util/std_expr.h>

#include <cegis/jsa/converters/counterexample.h>

#define HEAP_VAR_SIGNIFIER "heap"
#define CONCRETE_NODES_COMP_INDEX 0
#define ABSTRACT_NODES_COMP_INDEX 1
#define ABSTRACT_RANGES_COMP_INDEX 2
#define ITERATORS_COMP_INDEX 3
#define ITERATOR_COUNT_COMP_INDEX 4
#define LIST_HEAD_NODES_COMP_INDEX 5
#define LIST_COUNT_COMP_INDEX 6
#define NEXT_COMP_INDEX 0
#define PREV_COMP_INDEX 1
#define LIST_COMP_INDEX 2
#define VALUE_COMP_INDEX 3
#define MIN_COMP_INDEX 0
#define MAX_COMP_INDEX 1
#define SIZE_COMP_INDEX 2
#define NODE_COMP_INDEX 0
#define PREV_NODE_COMP_INDEX 1
#define ITERATOR_INDEX_COMP_INDEX 2
#define PREV_ITERATOR_INDEX_COMP_INDEX 3
#define ITERATOR_LIST_COMP_INDEX 4
#define NUM_ABSTRACT_HEAP_MEMBERS 7

namespace
{
bool is_heap(const jsa_counterexamplet::value_type &ass)
{
  return ID_struct == ass.second.id();
}
}

size_t count_heaps(const jsa_counterexamplet &ce)
{
  return std::count_if(ce.begin(), ce.end(), is_heap);
}

namespace
{
bool compare_assignment(const jsa_counterexamplet::value_type &lhs,
    const jsa_counterexamplet::value_type &rhs)
{
  return id2string(lhs.first) < id2string(rhs.first);
}

__CPROVER_jsa_word_t to_integer(const exprt &expr)
{
  const bv_arithmetict bv(expr);
  const mp_integer::llong_t value=bv.to_integer().to_long();
  return static_cast<__CPROVER_jsa_word_t >(value);
}

void read_element(__CPROVER_jsa_word_t &e, const exprt &value)
{
  e=to_integer(value);
}

template<class structt>
void make_zero(structt &value)
{
  value={};
}

void read_element(__CPROVER_jsa_concrete_nodet &e, const exprt &value)
{
  if (ID_struct != value.id()) return make_zero(e);
  const struct_exprt::operandst &ops=to_struct_expr(value).operands();
  assert(ops.size() > VALUE_COMP_INDEX);
  e.next=to_integer(ops[NEXT_COMP_INDEX]);
  e.previous=to_integer(ops[PREV_COMP_INDEX]);
  e.list=to_integer(ops[LIST_COMP_INDEX]);
  e.value=to_integer(ops[VALUE_COMP_INDEX]);
}

void read_element(__CPROVER_jsa_abstract_nodet &e, const exprt &value)
{
  if (ID_struct != value.id()) return make_zero(e);
  const struct_exprt::operandst &ops=to_struct_expr(value).operands();
  assert(ops.size() > VALUE_COMP_INDEX);
  e.next=to_integer(ops[NEXT_COMP_INDEX]);
  e.previous=to_integer(ops[PREV_COMP_INDEX]);
  e.list=to_integer(ops[LIST_COMP_INDEX]);
  e.value_ref=to_integer(ops[VALUE_COMP_INDEX]);
}

void read_element(__CPROVER_jsa_abstract_ranget &e, const exprt &value)
{
  if (ID_struct != value.id()) return make_zero(e);
  const struct_exprt::operandst &ops=to_struct_expr(value).operands();
  assert(ops.size() > SIZE_COMP_INDEX);
  e.min=to_integer(ops[MIN_COMP_INDEX]);
  e.max=to_integer(ops[MAX_COMP_INDEX]);
  e.size=to_integer(ops[SIZE_COMP_INDEX]);
}

void read_element(__CPROVER_jsa_iteratort &e, const exprt &value)
{
  if (ID_struct != value.id()) return make_zero(e);
  const struct_exprt::operandst &ops=to_struct_expr(value).operands();
  assert(ops.size() > ITERATOR_LIST_COMP_INDEX);
  e.node_id=to_integer(ops[NODE_COMP_INDEX]);
  e.previous_node_id=to_integer(ops[PREV_NODE_COMP_INDEX]);
  e.index=to_integer(ops[ITERATOR_INDEX_COMP_INDEX]);
  e.previous_index=to_integer(ops[PREV_ITERATOR_INDEX_COMP_INDEX]);
  e.list=to_integer(ops[ITERATOR_LIST_COMP_INDEX]);
}

void fill_null(__CPROVER_jsa_concrete_nodet *array, size_t count)
{
  assert(__CPROVER_JSA_MAX_CONCRETE_NODES >= count);
  const __CPROVER_jsa_concrete_nodet null_node={ __CPROVER_jsa_null,
      __CPROVER_jsa_null, __CPROVER_jsa_null, __CPROVER_jsa_null };
  while (count < __CPROVER_JSA_MAX_CONCRETE_NODES)
    array[count++]=null_node;
}

void fill_null(__CPROVER_jsa_abstract_nodet *array, const size_t count)
{
  assert(__CPROVER_JSA_MAX_ABSTRACT_NODES >= count);
  assert(count == 0);
}

void fill_null(__CPROVER_jsa_abstract_ranget *array, const size_t count)
{
  assert(__CPROVER_JSA_MAX_ABSTRACT_RANGES >= count);
  assert(count == 0);
}

void fill_null(__CPROVER_jsa_iteratort *array, size_t count)
{
  assert(__CPROVER_JSA_MAX_ITERATORS >= count);
  const __CPROVER_jsa_iteratort null_it={ __CPROVER_jsa_null,
      __CPROVER_jsa_null, 0, 0, __CPROVER_jsa_null };
  while (count < __CPROVER_JSA_MAX_ITERATORS)
    array[count++]=null_it;
}

void fill_null(__CPROVER_jsa_node_id_t *array, size_t count)
{
  assert(__CPROVER_JSA_MAX_LISTS >= count);
  while (count < __CPROVER_JSA_MAX_LISTS)
    array[count++]=__CPROVER_jsa_null;
}

template<class wordt>
void read_array(wordt *data, const exprt &value)
{
  if (ID_array != value.id()) return;
  size_t index=0;
  const exprt::operandst &ops=value.operands();
  for (const exprt &op : ops)
    read_element(data[index++], op);
  fill_null(data, ops.size());
}

void remove_padding(struct_exprt::operandst &ops, const typet &type)
{
  assert(!ops.empty());
  const struct_typet::componentst &comps=to_struct_type(type).components();
  assert(comps.size() == ops.size());
  for (int i=ops.size() - 1; i >= 0; --i)
    if (comps[i].get_bool(ID_C_is_padding))
      ops.erase(std::next(ops.begin(), i));
}
}

void retrieve_heaps(const jsa_counterexamplet &ce,
    __CPROVER_jsa_abstract_heapt *heaps)
{
  assert(std::is_sorted(ce.begin(), ce.end(), compare_assignment));
  size_t index=0;
  for (const jsa_counterexamplet::value_type &assignment : ce)
    if (is_heap(assignment))
    {
      const struct_exprt &value=to_struct_expr(assignment.second);
      __CPROVER_jsa_abstract_heapt &heap=heaps[index++];
      struct_exprt::operandst ops(value.operands());
      remove_padding(ops, value.type());
      assert(NUM_ABSTRACT_HEAP_MEMBERS == ops.size());
      read_array(heap.concrete_nodes, ops[CONCRETE_NODES_COMP_INDEX]);
      read_array(heap.abstract_nodes, ops[ABSTRACT_NODES_COMP_INDEX]);
      read_array(heap.abstract_ranges, ops[ABSTRACT_RANGES_COMP_INDEX]);
      read_array(heap.iterators, ops[ITERATORS_COMP_INDEX]);
      heap.iterator_count=to_integer(ops[ITERATOR_COUNT_COMP_INDEX]);
      read_array(heap.list_head_nodes, ops[LIST_HEAD_NODES_COMP_INDEX]);
      heap.list_count=to_integer(ops[LIST_COUNT_COMP_INDEX]);
    }
}

namespace
{
bool is_word(const jsa_counterexamplet::value_type &assignment)
{
  return !is_heap(assignment);
}
}

size_t count_words(const jsa_counterexamplet &ce)
{
  return std::count_if(ce.begin(), ce.end(), is_word);
}

void retrieve_words(const jsa_counterexamplet &ce, __CPROVER_jsa_word_t *words)
{
  assert(std::is_sorted(ce.begin(), ce.end(), compare_assignment));
  size_t index=0;
  for (const jsa_counterexamplet::value_type &assignment : ce)
    if (is_word(assignment)) words[index++]=to_integer(assignment.second);
}
