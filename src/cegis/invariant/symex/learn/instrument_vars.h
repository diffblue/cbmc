/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_INSTRUMENT_VARS_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_INSTRUMENT_VARS_H

#include <util/irep.h>

#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details
 */
typedef std::map<const irep_idt, size_t> operand_variable_idst;

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param num_temps
 * @param num_user_vars
 */
goto_programt::targett link_temp_vars(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos, const size_t num_temps,
    const size_t num_user_vars);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param num_user_vars
 * @param max_solution_size
 * @param pos
 */
void link_result_var(const symbol_tablet &st, goto_functionst &gf,
    size_t num_user_vars, size_t max_solution_size, goto_programt::targett pos);

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
 */
goto_programt::targett set_rops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param var_ids
 */
void link_user_program_variables(class invariant_programt &prog,
    const operand_variable_idst &var_ids);

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
size_t get_invariant_variable_ids(const class symbol_tablet &st,
    operand_variable_idst &ids);

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_INSTRUMENT_VARS_H
