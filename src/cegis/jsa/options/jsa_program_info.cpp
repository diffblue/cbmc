#include <util/bv_arithmetic.h>
#include <util/symbol_table.h>
#include <util/std_types.h>

#include <cegis/jsa/value/jsa_genetic_synthesis.h>
#include <cegis/jsa/options/jsa_program_info.h>

size_t to_size(const exprt &expr)
{
  const bv_arithmetict bv(expr);
  return static_cast<size_t>(bv.to_integer().to_long());
}

size_t get_size(const symbol_tablet &st, const char * const id)
{
  return to_size(to_array_type(st.lookup(id).type).size());
}

#define PRED_RELAY "__CPROVER_JSA_MAX_PRED_SIZE_RELAY"

size_t get_max_pred_size(const symbol_tablet &st)
{
  return get_size(st, PRED_RELAY);
}

#define QUERY_RELAY "__CPROVER_JSA_MAX_QUERY_SIZE_RELAY"

size_t get_max_query_size(const symbol_tablet &st)
{
  return get_size(st, QUERY_RELAY);
}

size_t get_max_inv_size()
{
  return 1;
}

size_t get_pred_instruction_set_size()
{
  return __CPROVER_JSA_NUM_PRED_INSTRUCTIONS;
}

size_t get_query_instruction_set_size()
{
  return __CPROVER_JSA_NUM_QUERY_INSTRUCTIONS;
}

size_t get_invariant_instruction_set_size()
{
  return __CPROVER_JSA_NUM_INV_INSTRUCTIONS;
}

size_t get_num_jsa_preds(const symbol_tablet &st)
{
  return get_size(st, JSA_PREDS);
}

#define MAX_IT "__CPROVER_JSA_MAX_ITERATORS_RELAY"

size_t get_max_iterators(const symbol_tablet &st)
{
  return get_size(st, MAX_IT);
}

#define MAX_LIST "__CPROVER_JSA_MAX_LISTS_RELAY"

size_t get_max_lists(const symbol_tablet &st)
{
  return get_size(st, MAX_LIST);
}

namespace
{
const size_t get_heap_comp_size(const symbol_tablet &st,
    const char * const name)
{
  const symbolt &symbol=st.lookup("tag-__CPROVER_jsa_abstract_heap");
  const struct_typet &struct_type=to_struct_type(symbol.type);
  const struct_typet::componentt &comp=struct_type.get_component(name);
  const array_typet &array_type=to_array_type(comp.type());
  return to_size(array_type.size());
}
}

size_t get_max_concrete_nodes(const symbol_tablet &st)
{
  return get_heap_comp_size(st, "concrete_nodes");
}

size_t get_max_abstract_nodes(const symbol_tablet &st)
{
  return 0;
}

#define MAX_NODES_PER_LIST "__CPROVER_JSA_MAX_NODES_PER_LIST_RELAY"

size_t get_max_nodes_per_list(const symbol_tablet &st)
{
  return get_size(st, MAX_NODES_PER_LIST);
}
