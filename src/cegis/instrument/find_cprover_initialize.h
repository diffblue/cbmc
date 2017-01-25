/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INSTRUMENT_FIND_CPROVER_INITIALIZE_H
#define CPROVER_CEGIS_INSTRUMENT_FIND_CPROVER_INITIALIZE_H

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

#endif // CPROVER_CEGIS_INSTRUMENT_FIND_CPROVER_INITIALIZE_H
