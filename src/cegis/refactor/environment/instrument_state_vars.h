/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_
#define CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_

#include <functional>

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param first
 * @param last
 * @param predicate
 */
void instrument_state_vars(
    goto_programt &body,
    const goto_programt::targett &first,
    const goto_programt::targett &last,
    std::function<bool(const goto_programt::instructiont &)> predicate);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param first
 * @param last
 */
void instrument_state_vars(
    goto_programt &body,
    const goto_programt::targett &first,
    const goto_programt::targett &last);

#endif /* CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_ */
