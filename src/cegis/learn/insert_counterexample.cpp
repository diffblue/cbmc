/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/cprover_prefix.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/find_cprover_initialize.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/learn/insert_counterexample.h>

#define CE_ARRAY_PREFIX CPROVER_PREFIX "ce_array_"
#define CE_VALUES_INDEX_PREFIX CPROVER_PREFIX "ce_values_index_"

zero_valuest get_zero_values(const symbol_tablet &st,
    const goto_programt::targetst &ce_locs)
{
  std::map<const irep_idt, exprt> zero_values;
  const source_locationt loc(default_cegis_source_location());
  const namespacet ns(st);
  null_message_handlert msg;
  for (const goto_programt::const_targett pos : ce_locs)
  {
    const irep_idt &marker=get_counterexample_marker(pos);
    const typet &type=get_affected_type(*pos);
    const exprt value(zero_initializer(type, loc, ns, msg));
    zero_values.insert(std::make_pair(marker, value));
  }
  return zero_values;
}

void normalise(const std::set<irep_idt> &ce_keys, const zero_valuest &zv,
    labelled_counterexamplest &ces)
{
  const exprt::operandst no_values;
  std::map<const irep_idt, size_t> sizes;
  for (labelled_counterexamplest::value_type &ce : ces)
  {
    for (const irep_idt &loc : ce_keys)
    {
      std::map<const irep_idt, size_t>::iterator sz=sizes.find(loc);
      if (sizes.end() == sz) sz=sizes.insert(std::make_pair(loc, 1)).first;
      size_t &size=sz->second;
      labelled_assignmentst::const_iterator values=ce.find(loc);
      if (ce.end() == values)
        values=ce.insert(std::make_pair(loc, no_values)).first;
      size=std::max(size, values->second.size());
    }
    assert(ce.size() == zv.size());
  }
  assert(sizes.size() == zv.size());
  for (labelled_counterexamplest::value_type &ce : ces)
    for (labelled_counterexamplest::value_type::value_type &ass : ce)
    {
      labelled_assignmentst::value_type::second_type &values=ass.second;
      const size_t current_size=values.size();
      const irep_idt &lbl=ass.first;
      const std::map<const irep_idt, size_t>::const_iterator it=sizes.find(lbl);
      assert(sizes.end() != it);
      const size_t target_size=it->second;
      assert(current_size <= target_size);
      const size_t missing=target_size - current_size;
      if (missing)
      {
        const std::map<const irep_idt, exprt>::const_iterator it=zv.find(lbl);
        assert(zv.end() != it);
        std::fill_n(std::back_inserter(values), missing, it->second);
      }
      assert(target_size == values.size());
    }
}

namespace
{
std::set<irep_idt> get_all_keys(const zero_valuest &zv)
{
  std::set<irep_idt> result;
  std::transform(zv.begin(), zv.end(), std::inserter(result, result.end()),
      [](const zero_valuest::value_type &v)
      { return v.first;});
  return result;
}

array_exprt to_values(const exprt::operandst &ops)
{
  assert(!ops.empty());
  const typet sz_type(signed_int_type());
  const constant_exprt sz_expr(from_integer(ops.size(), sz_type));
  const array_typet array_type(ops.front().type(), sz_expr);
  array_exprt result(array_type);
  copy(ops.begin(), ops.end(), std::back_inserter(result.operands()));
  return result;
}
}

array_valuest get_array_values(const labelled_counterexamplest &ces)
{
  const typet sz_type(signed_int_type());
  const constant_exprt ces_sz_expr(from_integer(ces.size(), sz_type));
  array_valuest result;
  for (const labelled_assignmentst &ce : ces)
    for (const labelled_assignmentst::value_type &ass : ce)
    {
      const array_exprt ass_values(to_values(ass.second));
      const irep_idt &loc=ass.first;
      array_valuest::iterator it=result.find(loc);
      if (result.end() == it)
      {
        const array_typet type(ass_values.type(), ces_sz_expr);
        it=result.insert(std::make_pair(loc, array_exprt(type))).first;
      }
      it->second.copy_to_operands(ass_values);
    }
  return result;
}

std::string get_ce_array_name(const irep_idt &loc_id)
{
  std::string base_name(CE_ARRAY_PREFIX);
  return base_name+=id2string(loc_id);
}

std::string get_ce_value_index_name(const irep_idt &loc)
{
  std::string label(CE_VALUES_INDEX_PREFIX);
  return label+=id2string(loc);
}

namespace
{
void add_array_declarations(symbol_tablet &st, goto_functionst &gf,
    const labelled_counterexamplest &ces, const goto_programt::targett &begin)
{
  const typet sz_type(signed_int_type());
  const constant_exprt sz_expr(from_integer(ces.size(), sz_type));
  const array_valuest array_values(get_array_values(ces));
  const labelled_counterexamplest::value_type &prototype=ces.front();
  goto_programt::targett pos=std::prev(begin);
  for (const labelled_counterexamplest::value_type::value_type &value : prototype)
  {
    const labelled_assignmentst::value_type::first_type loc_id=value.first;
    const array_valuest::const_iterator array_val=array_values.find(loc_id);
    assert(array_values.end() != array_val);
    const array_exprt &array_expr=array_val->second;
    const std::string base_name(get_ce_array_name(loc_id));
    pos=declare_cegis_meta_variable(st, gf, pos, base_name, array_expr.type());
    assert(array_expr.operands().size() == ces.size());
    pos=assign_cegis_meta_variable(st, gf, pos, base_name, array_expr);
  }
}

void add_array_indexes(const std::set<irep_idt> &ce_keys, symbol_tablet &st,
    goto_functionst &gf)
{
  goto_programt &body=get_entry_body(gf);
  const goto_programt::targett cprover_init(find_cprover_initialize(body));
  goto_programt::targett pos=cprover_init;
  const typet type(signed_int_type());
  pos=declare_cegis_meta_variable(st, gf, std::prev(pos), CE_ARRAY_INDEX, type);
  const source_locationt loc(default_cegis_source_location());
  const namespacet ns(st);
  null_message_handlert msg;
  const exprt zero(zero_initializer(type, loc, ns, msg));
  assign_cegis_meta_variable(st, gf, pos, CE_ARRAY_INDEX, zero);
  pos=cprover_init;
  for (const irep_idt &key : ce_keys)
  {
    const std::string label(get_ce_value_index_name(key));
    pos=declare_cegis_meta_variable(st, gf, pos, label, type);
    pos=assign_cegis_meta_variable(st, gf, pos, label, zero);
  }
}

plus_exprt increment(const symbol_exprt &symbol)
{
  const typet sz_type(signed_int_type());
  const constant_exprt one(from_integer(1, sz_type));
  return plus_exprt(symbol, one);
}

void add_ce_goto(symbol_tablet &st, goto_functionst &gf, const size_t num_ces,
    const goto_programt::targett &begin)
{
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos=find_last_instr(body);
  const std::string ce_index_name(get_cegis_meta_name(CE_ARRAY_INDEX));
  const symbol_exprt ce_index(st.lookup(ce_index_name).symbol_expr());
  const plus_exprt rhs(increment(ce_index));
  pos=assign_cegis_meta_variable(st, gf, pos, CE_ARRAY_INDEX, rhs);
  const source_locationt loc(default_cegis_source_location());
  pos=body.insert_after(pos);
  pos->source_location=loc;
  pos->type=goto_program_instruction_typet::GOTO;
  pos->targets.push_back(begin);
  const constant_exprt num_ces_sz(from_integer(num_ces, signed_int_type()));
  const binary_relation_exprt guard(ce_index, ID_lt, num_ces_sz);
  pos->guard=guard;
  pos=body.insert_after(pos);
  pos->source_location=loc;
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->guard=false_exprt();
  body.compute_target_numbers();
}

const index_exprt get_array_val_expr(const symbol_tablet &st,
    const irep_idt &loc)
{
  const std::string index_name(get_cegis_meta_name(CE_ARRAY_INDEX));
  const symbol_exprt index(st.lookup(index_name).symbol_expr());
  const std::string array_name(get_cegis_meta_name(get_ce_array_name(loc)));
  const symbol_exprt array(st.lookup(array_name).symbol_expr());
  const index_exprt ce(array, index);
  const std::string value_index(get_cegis_meta_name(get_ce_value_index_name(loc)));
  const symbol_exprt value_index_expr(st.lookup(value_index).symbol_expr());
  return index_exprt(ce, value_index_expr);
}

void assign_ce_values(symbol_tablet &st, goto_functionst &gf,
    const goto_programt::targetst &ce_locs)
{
  const typet sz_type(signed_int_type());
  const constant_exprt one(from_integer(1, sz_type));
  for (goto_programt::targett pos : ce_locs)
  {
    const irep_idt &label=get_counterexample_marker(pos);
    const index_exprt value(get_array_val_expr(st, pos->labels.front()));
    switch (pos->type)
    {
    case ASSIGN:
      to_code_assign(pos->code).rhs()=value;
      break;
    case DECL:
      pos=cegis_assign(st, gf, pos,
          st.lookup(get_affected_variable(*pos)).symbol_expr(), value);
      break;
    default:
      assert(!"Unsupported counterexample location type.");
    }
    const std::string value_index(get_cegis_meta_name(get_ce_value_index_name(label)));
    const symbol_exprt value_index_expr(st.lookup(value_index).symbol_expr());
    const plus_exprt inc(increment(value_index_expr));
    cegis_assign(st, gf, pos, value_index_expr, inc);
  }
}
}

void insert_counterexamples(symbol_tablet &st, goto_functionst &gf,
    labelled_counterexamplest ces, const goto_programt::targetst &ce_locs)
{
  assert(!ces.empty());
  const zero_valuest zero_values(get_zero_values(st, ce_locs));
  const std::set<irep_idt> ce_keys(get_all_keys(zero_values));
  normalise(ce_keys, zero_values, ces);
  goto_programt &body=get_entry_body(gf);
  const goto_programt::targett begin(find_cprover_initialize(body));
  add_array_declarations(st, gf, ces, begin);
  add_array_indexes(ce_keys, st, gf);
  add_ce_goto(st, gf, ces.size(), begin);
  assign_ce_values(st, gf, ce_locs);
}
