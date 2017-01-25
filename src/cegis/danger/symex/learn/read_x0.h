/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_LEARN_READ_X0_H
#define CPROVER_CEGIS_DANGER_SYMEX_LEARN_READ_X0_H

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param trace
 */
void danger_read_x0(class danger_goto_solutiont &result,
    const class danger_programt &prog, const class goto_tracet &trace);

/**
 * @brief
 *
 * @details
 *
 * @param ind
 * @param prog
 * @param trace
 */
void danger_read_x0(class program_individualt &ind, const danger_programt &prog,
    const goto_tracet &trace);

#endif // CPROVER_CEGIS_DANGER_SYMEX_LEARN_READ_X0_H
