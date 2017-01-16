/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>

#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/learn/insert_counterexample.h>

#define CE_ARRAY_PREFIX JSA_PREFIX "ce_array_"
#define CE_ARRAY_INDEX JSA_PREFIX "ce_array_index"

namespace
{
constant_exprt get_size_expr(const size_t size)
{
  return from_integer(size, signed_int_type());
}

typedef std::map<jsa_counterexamplet::key_type, array_exprt> array_valuest;
array_valuest get_array_values(const symbol_tablet &st,
    const jsa_counterexamplest &ces)
{
  const constant_exprt size_expr(get_size_expr(ces.size()));
  const jsa_counterexamplet &prototype=ces.front();
  array_valuest array_values;
  for (const jsa_counterexamplet::value_type &value : prototype)
  {
    const typet &org_type=value.second.type();
    const typet &element_type=replace_struct_by_symbol_type(st, org_type);
    const array_typet array_type(element_type, size_expr);
    array_values.insert(std::make_pair(value.first, array_exprt(array_type)));
  }
  for (const jsa_counterexamplet &ce : ces)
    for (const jsa_counterexamplet::value_type &value : ce)
      array_values[value.first].copy_to_operands(value.second);
  return array_values;
}

std::string get_array_name(const irep_idt &loc_id)
{
  std::string base_name(CE_ARRAY_PREFIX);
  return base_name+=id2string(loc_id);
}

void add_array_declarations(jsa_programt &program,
    const jsa_counterexamplest &ces)
{
  symbol_tablet &st=program.st;
  goto_functionst &gf=program.gf;
  goto_programt &body=get_entry_body(gf);
  const jsa_counterexamplet &prototype=ces.front();
  const array_valuest array_values(get_array_values(st, ces));
  const constant_exprt size_expr(get_size_expr(ces.size()));
  goto_programt::targett &pos=program.synthetic_variables;
  for (const jsa_counterexamplet::value_type &value : prototype)
  {
    const jsa_counterexamplet::value_type::first_type loc_id=value.first;
    const typet &org_type=value.second.type();
    const typet &element_type=replace_struct_by_symbol_type(st, org_type);
    const array_typet array_type(element_type, size_expr);
    const std::string base_name(get_array_name(loc_id));
    pos=body.insert_after(pos);
    declare_jsa_meta_variable(st, pos, base_name, array_type);
    const array_valuest::const_iterator array_val=array_values.find(loc_id);
    assert(array_values.end() != array_val);
    const array_exprt &array_expr=array_val->second;
    assert(array_expr.operands().size() == ces.size());
    pos=assign_jsa_meta_variable(st, gf, pos, base_name, array_val->second);
  }
}

void add_array_index(jsa_programt &prog)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett &pos=prog.synthetic_variables;
  pos=body.insert_after(pos);
  const typet type(signed_int_type());
  declare_jsa_meta_variable(st, pos, CE_ARRAY_INDEX, type);
  constant_exprt zero=from_integer(0, signed_int_type());
  pos=assign_jsa_meta_variable(st, gf, pos, CE_ARRAY_INDEX, zero);
}

symbol_exprt get_ce_array_index(const symbol_tablet &st)
{
  return st.lookup(get_cegis_meta_name(CE_ARRAY_INDEX)).symbol_expr();
}

void add_ce_goto(jsa_programt &prog, const size_t ces_size)
{
  goto_programt &body=get_entry_body(prog.gf);
  goto_programt::targett pos=std::next(prog.property_entailment, 2);
  pos=insert_before_preserve_labels(body, pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::ASSIGN;
  const symbol_exprt lhs(get_ce_array_index(prog.st));
  const typet &type=lhs.type();
  const plus_exprt inc(lhs, from_integer(1, type), type);
  pos->code=code_assignt(lhs, inc);
  pos=body.insert_after(pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::GOTO;
  pos->targets.push_back(std::next(prog.synthetic_variables));
  const binary_relation_exprt guard(lhs, ID_lt, get_size_expr(ces_size));
  pos->guard=guard;
  pos=body.insert_after(pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->guard=false_exprt();
  body.compute_target_numbers();
}

const index_exprt get_array_val_expr(const symbol_tablet &st,
    const irep_idt &loc)
{
  const std::string index_name(get_cegis_meta_name(CE_ARRAY_INDEX));
  const symbol_exprt index(st.lookup(index_name).symbol_expr());
  const std::string array_name(get_cegis_meta_name(get_array_name(loc)));
  const symbol_exprt array(st.lookup(array_name).symbol_expr());
  return index_exprt(array, index);
}

void assign_ce_values(jsa_programt &prog)
{
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  for (const goto_programt::targett &pos : prog.counterexample_locations)
  {
    assert(pos->labels.size() == 1u);
    const index_exprt value(get_array_val_expr(st, pos->labels.front()));
    switch (pos->type)
    {
    case ASSIGN:
      to_code_assign(pos->code).rhs()=value;
      break;
    case DECL:
      jsa_assign(st, gf, pos,
          st.lookup(get_affected_variable(*pos)).symbol_expr(), value);
      break;
    default:
      assert(!"Unsupported counterexample location type.");
    }
  }
}
}

void insert_counterexamples(jsa_programt &program,
    const jsa_counterexamplest &ces)
{
  assert(!ces.empty());
  assert(ces.front().size() == program.counterexample_locations.size());
  add_array_declarations(program, ces);
  add_array_index(program);
  add_ce_goto(program, ces.size());
  assign_ce_values(program);
}
