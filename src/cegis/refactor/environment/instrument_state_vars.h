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
 * @param first
 * @param last
 *
 * @return
 */
std::set<irep_idt> collect_state_vars(
    goto_programt::const_targett first,
    goto_programt::const_targett last);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 * @param state_vars
 * @param predicate
 */
void instrument_program_ops(
    goto_programt &body,
    goto_programt::targett pos,
    const std::set<irep_idt> &state_vars,
    std::function<bool(const typet &)> predicate);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 * @param state_vars
 */
void instrument_program_ops(
    goto_programt &body,
    goto_programt::targett pos,
    const std::set<irep_idt> &state_vars);

#endif /* CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_ */
