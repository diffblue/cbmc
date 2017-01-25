/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_PREPROCESS_REMOVE_LOOPS_AND_ASSERTION_H
#define CPROVER_CEGIS_INVARIANT_PREPROCESS_REMOVE_LOOPS_AND_ASSERTION_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param program
 */
void invariant_remove_loops_and_assertion(class invariant_programt &program);

/**
 * @brief
 *
 * @details
 *
 * @param instrs
 * @param instr
 * @param guard
 * @param body_begin
 * @param body_end
 */
void invariant_remove_loop(
    const class symbol_tablet &st,
    goto_programt::instructionst &instrs,
    const goto_programt::targett &instr,
    exprt &guard,
    goto_programt::targett &body_begin,
    goto_programt::targett &body_end);

#endif // CPROVER_CEGIS_INVARIANT_PREPROCESS_REMOVE_LOOPS_AND_ASSERTION_H
