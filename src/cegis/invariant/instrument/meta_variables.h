/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INVARIANT_META_VARIABLES_H_
#define CEGIS_INVARIANT_META_VARIABLES_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param base_name
 *
 * @return
 */
std::string get_invariant_meta_name(const std::string &base_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param insert_after_pos
 * @param base_name
 * @param type
 *
 * @return
 */
goto_programt::targett declare_invariant_variable(symbol_tablet &st,
    class goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const std::string &base_name, const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param full_name
 * @param type
 *
 * @return
 */
symbolt &create_invariant_symbol(symbol_tablet &st, const std::string &full_name,
    const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param insert_after_pos
 * @param lhs
 * @param rhs
 *
 * @return
 */
goto_programt::targett invariant_assign(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param insert_after_pos
 * @param base_name
 * @param value
 *
 * @return
 */
goto_programt::targett invariant_assign_user_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const irep_idt &name, const exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param insert_after_pos
 * @param base_name
 * @param value
 *
 * @return
 */
goto_programt::targett assign_invariant_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const std::string &base_name, const exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet invariant_meta_type();

/**
 * @brief
 *
 * @details
 *
 * @return
 */
source_locationt default_invariant_source_location();

#endif /* CEGIS_INVARIANT_META_VARIABLES_H_ */
