/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/cprover_prefix.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/counterexample_vars.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/collect_variables.h>

namespace
{
bool is_meta(const goto_programt::const_targett pos)
{
  const std::string &name=id2string(get_affected_variable(*pos));
  if(is_jsa_list(name) || is_jsa_iterator(name)) return false;
  return contains(name, CPROVER_PREFIX) || is_return_value_name(name);
}

bool is_const(const symbol_exprt &symbol_expr)
{
  return symbol_expr.type().get_bool(ID_C_constant);
}
}

void add_inductive_step_renondets(jsa_programt &prog)
{
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt::instructionst &body=get_entry_body(gf).instructions;
  const goto_programt::targett last=prog.base_case;
  goto_programt::targett pos=prog.base_case;
  for(goto_programt::targett it=body.begin(); it != last; ++it)
  {
    if(goto_program_instruction_typet::DECL != it->type) continue;
    const irep_idt &id=get_affected_variable(*it);
    if(is_meta(it)) continue;
    const symbol_exprt symbol(st.lookup(id).symbol_expr());
    if(is_const(symbol)) continue;
    const typet &type=symbol.type();
    pos=jsa_assign(st, gf, pos, symbol, side_effect_expr_nondett(type));
    prog.inductive_step_renondets.push_back(pos);
  }
}

#define CE_MARKER_PREFIX JSA_PRED_PREFIX "ce_marker_"

void collect_counterexample_vars(jsa_programt &prog)
{
  goto_programt::targetst &locs=prog.counterexample_locations;
  goto_programt &body=get_entry_body(prog.gf);
  collect_counterexample_locations(locs, CE_MARKER_PREFIX, body, is_meta);
}
