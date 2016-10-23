/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_INSTRUCTIONSET_EXECUTE_CEGIS_PROGRAM_H_
#define CEGIS_REFACTOR_INSTRUCTIONSET_EXECUTE_CEGIS_PROGRAM_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param processor
 * @param program_name
 * @param size
 */
void declare_cegis_program(
    class symbol_tablet &st,
    class goto_functionst &gf,
    const std::string &processor,
    const std::string &program_name,
    const size_t size);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param processor
 * @param program_name
 *
 * @return
 */
goto_programt::targett call_processor(
    const symbol_tablet &st,
    goto_programt &body,
    goto_programt::targett pos,
    const std::string &processor,
    const std::string &program_name);

#endif /* CEGIS_REFACTOR_INSTRUCTIONSET_EXECUTE_CEGIS_PROGRAM_H_ */
