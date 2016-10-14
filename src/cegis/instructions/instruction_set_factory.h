/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

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
 * @param body
 * @return
 */
instruction_sett extract_instruction_set(const goto_programt &body);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param first_prefix
 * @param last_prefix
 * @param single_prefix
 * @return
 */
instruction_sett extract_instruction_set(
    const goto_programt &body,
    const std::string &first_prefix,
    const std::string &last_prefix,
    const std::string &single_prefix);

#endif /* CEGIS_DANGER_INSTRUCTION_SET_FACTORY_H_ */
