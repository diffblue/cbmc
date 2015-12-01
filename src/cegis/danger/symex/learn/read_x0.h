/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_READ_X0_H_
#define CEGIS_DANGER_READ_X0_H_

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

#endif /* CEGIS_DANGER_READ_X0_H_ */
