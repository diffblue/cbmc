/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_FIND_CPROVER_INITIALIZE_H_
#define CEGIS_FIND_CPROVER_INITIALIZE_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param body
 *
 * @return
 */
goto_programt::targett find_cprover_initialize(goto_programt &body);

/**
 * @brief
 *
 * @details
 *
 * @param body
 *
 * @return
 */
goto_programt::targett find_last_instr(goto_programt &body);

#endif /* CEGIS_FIND_CPROVER_INITIALIZE_H_ */
