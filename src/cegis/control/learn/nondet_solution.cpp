#include <algorithm>

#include <cegis/control/value/control_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/find_cprover_initialize.h>
#include <cegis/control/learn/nondet_solution.h>

namespace
{
bool is_sol_assign(const goto_programt::instructiont &instr)
{
  if (goto_program_instruction_typet::ASSIGN != instr.type) return false;
  const std::string &var=id2string(get_affected_variable(instr));
  return CEGIS_CONTROL_SOLUTION_VAR_NAME == var;
}

void remove_solution_assignment_from_cprover_init(goto_functionst &gf)
{
  goto_programt::instructionst &i=get_body(gf, CPROVER_INIT).instructions;
  const goto_programt::targett end(i.end());
  const goto_programt::targett pos=std::find_if(i.begin(), end, is_sol_assign);
  assert(end != pos);
  i.erase(pos);
}
}

void nondet_control_solution(const symbol_tablet &st, goto_functionst &gf)
{
  const irep_idt name(CEGIS_CONTROL_SOLUTION_VAR_NAME);
  const symbolt &symbol=st.lookup(name);
  const side_effect_expr_nondett value(symbol.type);
  const symbol_exprt solution_var(symbol.symbol_expr());
  goto_programt &body=get_entry_body(gf);
  const goto_programt::targett pos(find_cprover_initialize(body));
  cegis_assign_user_variable(st, gf, std::prev(pos), name, value);
  // TODO: Extract a_size, b_size and assign
  remove_solution_assignment_from_cprover_init(gf);
}
