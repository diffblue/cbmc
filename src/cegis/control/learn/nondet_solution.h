/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_LEARN_NONDET_SOLUTION_H
#define CPROVER_CEGIS_CONTROL_LEARN_NONDET_SOLUTION_H

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 */
void nondet_control_solution(
    const class symbol_tablet &st,
    class goto_functionst &gf);

#endif // CPROVER_CEGIS_CONTROL_LEARN_NONDET_SOLUTION_H
