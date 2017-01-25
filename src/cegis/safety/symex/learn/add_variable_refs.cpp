/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>
#include <cegis/safety/symex/learn/add_variable_refs.h>

void add_safety_learning_variable_refs(invariant_programt &prog,
    const operand_variable_idst &var_ids, const size_t max_sz)
{
  link_user_program_variables(prog, var_ids);
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  const size_t num_vars=var_ids.size();
  const invariant_programt::const_invariant_loopst loops(
      static_cast<const invariant_programt &>(prog).get_loops());
  for (const invariant_programt::invariant_loopt * const loop : loops)
  {
    link_result_var(st, gf, num_vars, max_sz, loop->meta_variables.Ix);
    link_result_var(st, gf, num_vars, max_sz, loop->meta_variables.Ix_prime);
  }
}
