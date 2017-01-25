/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INSTRUMENT_INSTRUMENT_VAR_OPS_H
#define CPROVER_CEGIS_INSTRUMENT_INSTRUMENT_VAR_OPS_H

#include <goto-programs/goto_program.h>

typedef std::map<const irep_idt, size_t> operand_variable_idst;
typedef bool (*is_op_variablet)(const irep_idt &id, const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @params ids
 *
 * @return
 */
size_t get_variable_op_ids(const class symbol_tablet &st,
    operand_variable_idst &ids);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @params ids
 * @param is_op_variable
 *
 * @return
 */
size_t get_variable_op_ids(const class symbol_tablet &st,
    operand_variable_idst &ids, is_op_variablet is_op_variable);

/**
 * @brief
 *
 * @details
 *
 * @param id
 * @param type
 *
 * @return
 */
bool is_instrumentable_user_variable(const irep_idt &id, const typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param var_ids
 * @param is_op_variable
 * @param begin
 * @param end
 */
void link_user_program_variable_ops(const symbol_tablet &st, class goto_functionst &gf,
    const operand_variable_idst &var_ids, const is_op_variablet is_op_variable,
    goto_programt::targett begin, goto_programt::targett end);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param var_ids
 * @param begin
 * @param end
 */
void link_user_program_variable_ops(
    const symbol_tablet &st, class goto_functionst &gf,
    const operand_variable_idst &var_ids,
    goto_programt::targett begin, goto_programt::targett end);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param name
 * @param id
 *
 * @return
 */
goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param ops_array
 * @param name
 * @param id
 *
 * @return
 */
goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const char * const ops_array, const irep_idt &name, const unsigned int id);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param ops_array
 * @param rhs
 * @param id
 *
 * @return
 */
goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const char * const ops_array, const exprt &rhs, const unsigned int id);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param rhs
 * @param id
 *
 * @return
 */
goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos, const exprt &rhs,
    const unsigned int id);


/**
 * @brief
 *
 * @details
 *
 * @return
 */
source_locationt default_cegis_source_location();

#endif // CPROVER_CEGIS_INSTRUMENT_INSTRUMENT_VAR_OPS_H
