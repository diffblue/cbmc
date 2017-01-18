#include <algorithm>

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/instrument/find_cprover_initialize.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/learn/insert_counterexample.h>
#include <cegis/refactor/options/refactor_program.h>
#include <cegis/refactor/learn/instrument_counterexamples.h>

namespace
{
goto_programt::targetst unify(
    const refactor_programt::counterexample_locationst &locs)
{
  goto_programt::targetst result;
  for (const refactor_programt::counterexample_locationst::value_type &entry : locs)
  {
    const goto_programt::targetst &rhs=entry.second;
    std::copy(rhs.begin(), rhs.end(), std::back_inserter(result));
  }
  return result;
}

std::set<irep_idt> get_all_keys(
    const refactor_programt::counterexample_locationst &locs)
{
  std::set<irep_idt> keys;
  for (const refactor_programt::counterexample_locationst::value_type &entry : locs)
  {
    const goto_programt::targetst &rhs=entry.second;
    std::transform(rhs.begin(), rhs.end(), std::inserter(keys, keys.begin()),
        [](const goto_programt::const_targett pos)
        { return get_counterexample_marker(pos);});
  }
  return keys;
}

void create_ce_arrays(symbol_tablet &st, goto_functionst &gf,
    const labelled_counterexamplest &ces)
{
  if (ces.empty()) return;
  const typet sz_type(signed_int_type());
  const constant_exprt sz_expr(from_integer(ces.size(), sz_type));
  const array_valuest array_values(get_array_values(ces));
  const labelled_counterexamplest::value_type &prototype=ces.front();
  for (const labelled_counterexamplest::value_type::value_type &value : prototype)
  {
    const labelled_assignmentst::value_type::first_type loc_id=value.first;
    const array_valuest::const_iterator array_val=array_values.find(loc_id);
    assert(array_values.end() != array_val);
    const array_exprt &array_expr=array_val->second;
    const std::string name(get_ce_array_name(loc_id));
    assert(array_expr.operands().size() == ces.size());
    declare_global_meta_variable(st, gf, name, array_expr);
  }
}

void create_ce_array_indexes(const std::set<irep_idt> &ce_keys,
    symbol_tablet &st, goto_functionst &gf)
{
  const exprt zero(gen_zero(signed_int_type()));
  declare_global_meta_variable(st, gf, CE_ARRAY_INDEX, zero);
  goto_programt &body=get_body(gf, CONSTRAINT_CALLER_ID);
  goto_programt::targett pos=body.instructions.begin();
  const goto_programt::targett init=body.insert_before(pos);
  pos=init;
  const source_locationt &loc=pos->source_location;
  const irep_idt &function=pos->function;
  for (const irep_idt &key : ce_keys)
  {
    const std::string name(get_ce_value_index_name(key));
    declare_global_meta_variable(st, name, zero.type());
    pos=cegis_assign(st, body, pos, st.lookup(name).symbol_expr(), zero, loc);
    pos->function=function;
  }
  body.instructions.erase(init);
}

void add_ce_goto(const symbol_tablet &st, goto_functionst &gf,
    const size_t num_ces)
{
  goto_programt &body=get_body(gf, CONSTRAINT_CALLER_ID);
  goto_programt::targett pos=find_last_instr(body);
  const source_locationt &loc=pos->source_location;
  const irep_idt &function=pos->function;
  const symbol_exprt ce_index(st.lookup(CE_ARRAY_INDEX).symbol_expr());
  const plus_exprt rhs(ce_index, from_integer(1, ce_index.type()));
  pos=cegis_assign(st, body, pos, ce_index, rhs, loc);
  pos->function=function;
  pos=insert_after_preserving_source_location(body, pos);
  pos->type=goto_program_instruction_typet::GOTO;
  pos->targets.push_back(body.instructions.begin());
  const constant_exprt num_ces_sz(from_integer(num_ces, signed_int_type()));
  pos->guard=binary_relation_exprt(ce_index, ID_lt, num_ces_sz);
  pos=insert_after_preserving_source_location(body, pos);
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->guard=false_exprt();
  body.compute_target_numbers();
}

const index_exprt get_array_val_expr(const symbol_tablet &st,
    const irep_idt &loc)
{
  const symbol_exprt index(st.lookup(CE_ARRAY_INDEX).symbol_expr());
  const symbol_exprt array(st.lookup(get_ce_array_name(loc)).symbol_expr());
  const index_exprt ce(array, index);
  const std::string value_index(get_ce_value_index_name(loc));
  const symbol_exprt value_index_expr(st.lookup(value_index).symbol_expr());
  return index_exprt(ce, value_index_expr);
}

void assign_ce_values(symbol_tablet &st, goto_functionst &gf,
    const refactor_programt::counterexample_locationst &ce_locs)
{
  for (const refactor_programt::counterexample_locationst::value_type ce_loc : ce_locs)
  {
    for (goto_programt::targett pos : ce_loc.second)
    {
      const irep_idt &label=get_counterexample_marker(pos);
      const index_exprt value(get_array_val_expr(st, label));
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
      const std::string value_index_name(get_ce_value_index_name(label));
      const symbol_exprt value_index(st.lookup(value_index_name).symbol_expr());
      const plus_exprt inc(value_index, from_integer(1, value_index.type()));
      cegis_assign(st, gf, pos, value_index, inc);
    }
  }
}
}

void instrument_counterexamples(refactor_programt &prog,
    refactor_counterexamplest ces)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  const refactor_programt::counterexample_locationst &ce_locs=
      prog.counterexample_locations;
  const goto_programt::targetst unified(unify(ce_locs));
  const std::set<irep_idt> all_keys(get_all_keys(ce_locs));
  const zero_valuest zeroes(get_zero_values(st, unified));
  normalise(all_keys, zeroes, ces);
  create_ce_arrays(st, gf, ces);
  create_ce_array_indexes(all_keys, st, gf);
  add_ce_goto(st, gf, ces.size());
  assign_ce_values(st, gf, ce_locs);
}
