/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_INSTRUMENT_TEMPS_HELPER_H
#define CPROVER_CEGIS_JSA_INSTRUMENT_TEMPS_HELPER_H

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

#endif // CPROVER_CEGIS_JSA_INSTRUMENT_TEMPS_HELPER_H
