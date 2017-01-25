/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/refactor/environment/instrument_state_vars.h>

namespace
{
class var_findert: public const_expr_visitort
{
  std::set<irep_idt> &vars;
public:
  var_findert(std::set<irep_idt> &vars) :
      vars(vars)
  {
  }

  virtual ~var_findert()=default;

  virtual void operator()(const exprt &expr)
  {
    if (ID_symbol != expr.id()) return;
    if (ID_code == expr.type().id()) return;
    // TODO: Follow function calls
    vars.insert(to_symbol_expr(expr).get_identifier());
  }
};
}

void collect_state_vars(std::set<irep_idt> &result,
    goto_programt::const_targett first, const goto_programt::const_targett last)
{
  var_findert visitor(result);
  for (; first != last; ++first)
  {
    first->code.visit(visitor);
    first->guard.visit(visitor);
  }
}

void instrument_program_ops(goto_programt &body, goto_programt::targett pos,
    const std::set<irep_idt> &state_vars,
    const std::function<bool(const typet &)> predicate)
{
  // TODO: Implement
  assert(false);
}

namespace
{
bool use_all(const typet &instr)
{
  return true;
}
}

void instrument_program_ops(goto_programt &body, goto_programt::targett pos,
    const std::set<irep_idt> &state_vars)
{
  instrument_program_ops(body, pos, state_vars, use_all);
}
