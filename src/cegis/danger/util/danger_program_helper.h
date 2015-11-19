/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_PROGRAM_HELPER_H_
#define CEGIS_DANGER_PROGRAM_HELPER_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param gf
 *
 * @return
 */
class goto_programt &get_danger_body(class goto_functionst &gf);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 *
 * @return
 */
const goto_programt &get_danger_body(const goto_functionst &gf);

/**
 * @brief
 *
 * @details
 *
 * @param instr
 *
 * @return
 */
const irep_idt &get_affected_variable(const goto_programt::instructiont &instr);

/**
 * @brief
 *
 * @details
 *
 * @param target
 *
 * @return
 */
bool is_nondet(const goto_programt::targett &target);

/**
 * @brief
 *
 * @details
 *
 * @param name
 * @param type
 *
 * @return
 */
bool is_global_const(const irep_idt &name, const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param name
 * @param type
 *
 * @return
 */
bool is_danger_user_variable(const irep_idt &name, const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param original_offset
 * @param new_offset
 * @param target
 */
goto_programt::targett fix_target_by_offset(
    const goto_programt::const_targett &original_offset,
    goto_programt::targett new_offset,
    const goto_programt::const_targett &target);

#endif /* CEGIS_DANGER_PROGRAM_HELPER_H_ */
