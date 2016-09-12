#include <cegis/control/value/control_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/find_cprover_initialize.h>
#include <cegis/control/learn/nondet_solution.h>

void nondet_control_solution(const symbol_tablet &st, goto_functionst &gf)
{
  const irep_idt name(CEGIS_CONTROL_SOLUTION_VAR_NAME);
  const symbolt &symbol=st.lookup(name);
  const side_effect_expr_nondett value(symbol.type);
  const symbol_exprt solution_var(symbol.symbol_expr());
  goto_programt &body=get_entry_body(gf);
  const goto_programt::targett pos(find_cprover_initialize(body));
  cegis_assign_user_variable(st, gf, pos, name, value);
}
