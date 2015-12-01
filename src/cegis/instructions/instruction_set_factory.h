/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_INSTRUCTION_SET_FACTORY_H_
#define CEGIS_DANGER_INSTRUCTION_SET_FACTORY_H_

#include <goto-programs/goto_program.h>

typedef std::map<size_t, goto_programt::instructionst> instruction_sett;

/**
 * @brief
 *
 * @details
 *
 * @param instruction_set
 * @param body
 */
void extract_instruction_set(instruction_sett &instruction_set,
    const goto_programt &body);

#endif /* CEGIS_DANGER_INSTRUCTION_SET_FACTORY_H_ */
