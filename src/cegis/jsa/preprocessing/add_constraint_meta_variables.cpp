/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>

namespace
{
#if 0
symbolt &create_jsa_symbol(symbol_tablet &st, const std::string &full_name,
    const typet &type)
{
  symbolt new_symbol;
  new_symbol.name=full_name;
  new_symbol.type=type;
  new_symbol.base_name=full_name;
  new_symbol.pretty_name=new_symbol.base_name;
  new_symbol.location=jsa_builtin_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=JSA_MODULE;
  new_symbol.is_thread_local=true;
  new_symbol.is_static_lifetime=false;
  new_symbol.is_file_local=true;
  new_symbol.is_lvalue=true;
  assert(!st.add(new_symbol));
  return st.lookup(new_symbol.name);
}
#endif

void declare_lambda(jsa_programt &p, goto_programt &body)
{
  const goto_programt::targett pos=body.insert_after(body.instructions.begin());
  const typet type(jsa_word_type());
  declare_jsa_meta_variable(p.st, pos, JSA_LAMBDA_OP, type);
}
}

void declare_jsa_meta_variable(symbol_tablet &st,
    const goto_programt::targett &decl, const std::string &base_name,
    const typet &type)
{
  const std::string symbol_name(get_cegis_meta_name(base_name));
  create_cegis_symbol(st, symbol_name, type);
  const symbol_exprt symbol(symbol_name, type);
  decl->type=goto_program_instruction_typet::DECL;
  decl->code=code_declt(symbol);
  decl->source_location=jsa_builtin_source_location();
}

goto_programt::targett assign_jsa_meta_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &pos,
    const std::string &base_name, const exprt &expr_value)
{
  const std::string name(get_cegis_meta_name(base_name));
  const symbol_exprt lhs(st.lookup(name).symbol_expr());
  return jsa_assign(st, gf, pos, lhs, expr_value);
}

goto_programt::targett jsa_assign(const symbol_tablet &st, goto_functionst &gf,
    const goto_programt::targett &pos, const exprt &lhs, const exprt &rhs)
{
  const source_locationt loc(jsa_builtin_source_location());
  return cegis_assign(st, gf, pos, lhs, rhs, loc);
}

void add_jsa_constraint_meta_variables(jsa_programt &p)
{
  symbol_tablet &st=p.st;
  goto_programt &body=get_entry_body(p.gf);
  const typet type(c_bool_type());
  declare_lambda(p, body);
  p.base_case=insert_before_preserve_labels(body, p.body.first);
  declare_jsa_meta_variable(st, p.base_case, JSA_BASE_CASE, type);
  p.inductive_assumption=body.insert_after(p.base_case);
  declare_jsa_meta_variable(st, p.inductive_assumption, JSA_IND_ASSUME, type);
  p.inductive_step=insert_before_preserve_labels(body, p.body.second);
  declare_jsa_meta_variable(st, p.inductive_step, JSA_IND_STEP, type);
  p.property_entailment=insert_before_preserve_labels(body, p.body.second);
  declare_jsa_meta_variable(st, p.property_entailment, JSA_PROP_ENTAIL, type);
  p.body.second=p.property_entailment;
}
