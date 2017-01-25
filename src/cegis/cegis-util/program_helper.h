/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_PROGRAM_HELPER_H
#define CPROVER_CEGIS_CEGIS_UTIL_PROGRAM_HELPER_H

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
class goto_programt &get_entry_body(class goto_functionst &gf);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 *
 * @return
 */
const goto_programt &get_entry_body(const goto_functionst &gf);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param func_name
 *
 * @return
 */
goto_programt &get_body(
    goto_functionst &gf,
    const std::string &func_name);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param pos
 *
 * @return
 */
goto_programt &get_body(
    goto_functionst &gf,
    goto_programt::const_targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param func_name
 *
 * @return
 */
const goto_programt &get_body(
    const goto_functionst &gf,
    const std::string &func_name);

/**
 * @brief
 *
 * @details
 *
 * @param target
 * @param end
 *
 * @return
 */
bool is_nondet(
    goto_programt::const_targett target,
    goto_programt::const_targett end);

/**
 * @brief
 *
 * @details
 *
 * @param name
 *
 * @return
 */
bool is_return_value_name(const std::string &name);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @return
 */
goto_programt::targetst find_nondet_instructions(goto_programt &body);

/**
 * @brief
 *
 * @details
 *
 * @param instr
 *
 * @return
 */
const typet &get_affected_type(const goto_programt::instructiont &instr);

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
 * @param body
 * @param from
 * @param to
 */
void move_labels(
    goto_programt::instructionst &body,
    const goto_programt::targett &from,
    const goto_programt::targett &to);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param from
 * @param to
 */
void move_labels(
    goto_programt &body,
    const goto_programt::targett &from,
    const goto_programt::targett &to);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param target
 *
 * @return
 */
goto_programt::targett insert_before_preserve_labels(
    goto_programt &body,
    const goto_programt::targett &target);

/**
 * @brief
 *
 * @details
 *
 * @param loc
 *
 * @return
 */
bool is_builtin(const source_locationt &loc);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param full_name
 * @param base_name
 * @param type
 *
 * @return
 */
symbolt &create_local_cegis_symbol(symbol_tablet &st, const std::string &full_name,
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
symbolt &create_cegis_symbol(symbol_tablet &st, const std::string &full_name,
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
goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param instr
 * @param lhs
 * @param rhs
 * @param loc
 */
void cegis_assign(const symbol_tablet &st, goto_programt::instructiont &instr,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param insert_after_pos
 * @param lhs
 * @param rhs
 * @param loc
 *
 * @return
 */
goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc);

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
 * @param loc
 *
 * @return
 */
goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc);

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
goto_programt::targett cegis_assign_user_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const irep_idt &name, const exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param insert_after_pos
 * @param func_name
 * @param var_name
 * @param value
 *
 * @return
 */
goto_programt::targett cegis_assign_local_variable(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &insert_after_pos,
    const std::string &func_name, const std::string &var_name,
    const exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 */
void remove_return(
    goto_programt &body,
    goto_programt::targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 * @param func_id
 * @param value
 *
 * @return
 */
goto_programt::targett add_return_assignment(
    goto_programt &body,
    goto_programt::targett pos,
    const irep_idt &func_id,
    const exprt &value);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 *
 * @return
 */
goto_programt::targett insert_after_preserving_source_location(
    goto_programt &body,
    goto_programt::targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param pos
 *
 * @return
 */
goto_programt::targett insert_before_preserving_source_location(
    goto_programt &body,
    goto_programt::targett pos);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param symbol
 * @param value
 */
void assign_in_cprover_init(
    goto_functionst &gf,
    symbolt &symbol,
    const exprt &value);

#endif // CPROVER_CEGIS_CEGIS_UTIL_PROGRAM_HELPER_H
