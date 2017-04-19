/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/cprover_prefix.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/inline_user_program.h>
#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/control/value/control_vars.h>
#include <cegis/control/simplify/remove_unused_elements.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/preprocessing/control_preprocessing.h>
#include <goto-programs/remove_returns.h>

#define TMP_MARKER "$tmp"

// XXX: Debug
#include <iostream>
// XXX: Debug

control_preprocessingt::control_preprocessingt(const symbol_tablet &st,
    const goto_functionst &gf) :
    control_program(st, gf)
{
}

namespace
{
const char * const excluded_functions[]= {
    "verify_stability_closedloop_using_dslib", "check_stability_closedloop",
    "fxp_double_to_fxp", "fxp_to_double", "ft_closedloop_series", "poly_mult",
    "poly_sum", "internal_pow", "fxp_check", "fxp_control_floatt_to_fxp",
    "main", "validation", "double_matrix_multiplication", "double_sub_matrix",
    "check_stability" };

bool is_meta(const goto_programt::const_targett pos)
{
  if(default_cegis_meta_criterion(pos)) return true;
  const source_locationt &loc=pos->code.source_location();
  const std::string &func=id2string(loc.get_function());
  for(const char * const excluded : excluded_functions)
    if(contains(func, excluded)) return true;
  if((goto_program_instruction_typet::ASSIGN != pos->type
      && goto_program_instruction_typet::DECL != pos->type)
      || !pos->code.has_operands()
      || (pos->code.has_operands() && ID_symbol != pos->code.op0().id()))
    return false;
  const std::string &var=id2string(get_affected_variable(*pos));
  if(contains(var, TMP_MARKER) || contains(var, RETURN_VALUE_SUFFIX)
      || contains(var, CPROVER_PREFIX)) return true;
  return CEGIS_CONTROL_SOLUTION_VAR_NAME == var
      || CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME == var;
}

void add_explicit_nondet_for_extern_vars(const symbol_tablet &st,
    goto_functionst &gf)
{
  goto_programt &entry_body=get_entry_body(gf);
  goto_programt &init_body=get_body(gf, CPROVER_INIT);
  goto_programt::targett entry_pos=entry_body.instructions.begin();
  goto_programt::targett init_pos=std::prev(init_body.instructions.end(), 1);
  for(const symbol_tablet::symbolst::value_type &id_and_symbol : st.symbols)
  {
    const symbolt &symbol=id_and_symbol.second;
    const std::string &name=id2string(id_and_symbol.first);
    if(!symbol.is_extern || contains(name, CPROVER_PREFIX)) continue;
    const bool is_solution_var=CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME == name
        || CEGIS_CONTROL_SOLUTION_VAR_NAME == name;
    goto_programt &body=is_solution_var ? init_body : entry_body;
    goto_programt::targett &pos=is_solution_var ? init_pos : entry_pos;
    const source_locationt &loc=pos->source_location;
    if(is_solution_var) pos=body.insert_before(pos);
    else pos=body.insert_after(pos);
    pos->source_location=loc;
    pos->type=goto_program_instruction_typet::ASSIGN;
    const side_effect_expr_nondett rhs(symbol.type);
    pos->code=code_assignt(symbol.symbol_expr(), rhs);
  }
  entry_body.update();
}
}

void control_preprocessingt::operator ()()
{
  symbol_tablet &st=control_program.st;
  goto_functionst &gf=control_program.gf;
  remove_unused_elements(st, gf);
  inline_user_program(st, gf);
  goto_programt::targetst &locs=control_program.counterexample_locations;
  goto_programt &body=get_entry_body(gf);
  add_explicit_nondet_for_extern_vars(st, gf);
  collect_counterexample_locations(locs, body, is_meta);
  // XXX: Debug
  for(const goto_programt::const_targett target : locs)
  {
    std::cout << "<ce>" << target->code.pretty() << "</ce>" << std::endl;
  }
  // XXX: Debug
  propagate_controller_sizes(st, gf);
}

void control_preprocessingt::operator ()(const size_t max_length) const
{
}

size_t control_preprocessingt::get_min_solution_size() const
{
  return 1u;
}

const control_programt &control_preprocessingt::get_program() const
{
  return control_program;
}
