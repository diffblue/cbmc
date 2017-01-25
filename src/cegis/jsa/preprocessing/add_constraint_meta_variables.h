/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_PREPROCESSING_ADD_CONSTRAINT_META_VARIABLES_H
#define CPROVER_CEGIS_JSA_PREPROCESSING_ADD_CONSTRAINT_META_VARIABLES_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param decl
 * @param base_name
 */
void declare_jsa_meta_variable(
    symbol_tablet &st,
    const goto_programt::targett &decl,
    const std::string &base_name,
    const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param pos
 * @param base_name
 * @param expr_value
 */
goto_programt::targett assign_jsa_meta_variable(
    const symbol_tablet &st,
    goto_functionst &gf,
    const goto_programt::targett &pos,
    const std::string &base_name,
    const exprt &expr_value);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param pos
 * @param lhs
 * @param rhs
 */
goto_programt::targett jsa_assign(
    const symbol_tablet &st,
    goto_functionst &gf,
    const goto_programt::targett &pos,
    const exprt &lhs,
    const exprt &rhs);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
void add_jsa_constraint_meta_variables(class jsa_programt &prog);

#endif // CPROVER_CEGIS_JSA_PREPROCESSING_ADD_CONSTRAINT_META_VARIABLES_H
