/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_META_VARIABLES_H_
#define CEGIS_META_VARIABLES_H_

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
std::string get_cegis_meta_name(const std::string &base_name);

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
goto_programt::targett declare_cegis_meta_variable(symbol_tablet &st,
    class goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const std::string &base_name, const typet &type);

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
goto_programt::targett assign_cegis_meta_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const std::string &base_name, const exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet cegis_default_integer_type();

/**
 * @brief
 *
 * @details
 *
 * @param num_vars
 * @param num_consts
 * @param max_solution_size
 * @return
 */
std::string get_cegis_code_prefix(
    size_t num_vars,
    size_t num_consts,
    size_t max_solution_size);

#endif /* CEGIS_META_VARIABLES_H_ */
