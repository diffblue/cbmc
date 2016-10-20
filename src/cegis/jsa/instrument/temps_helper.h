/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_TEMPS_HELPER_H_
#define CEGIS_JSA_TEMPS_HELPER_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
goto_programt::targett zero_jsa_temps(
    class jsa_programt &prog,
    goto_programt::targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param result_ops
 *
 * @return
 */
void add_zero_jsa_temps_to_pred_exec(jsa_programt &prog);

/**
 * @brief
 *
 * @details
 *
 * @param st
 */
size_t count_tmps(const symbol_tablet &st);

#endif /* CEGIS_JSA_TEMPS_HELPER_H_ */
