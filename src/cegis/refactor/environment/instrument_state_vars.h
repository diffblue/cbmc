/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_
#define CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param first
 * @param last
 */
void instrument_state_vars(
    goto_programt::const_targett first,
    goto_programt::const_targett last);

#endif /* CEGIS_REFACTOR_ENVIRONMENT_INSTRUMENT_STATE_VARS_H_ */
