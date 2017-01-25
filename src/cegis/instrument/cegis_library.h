/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INSTRUMENT_CEGIS_LIBRARY_H
#define CPROVER_CEGIS_INSTRUMENT_CEGIS_LIBRARY_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param num_vars
 * @param num_consts
 * @param max_solution_size
 * @param func_name
 */
std::string get_cegis_library_text(size_t num_vars, size_t num_consts,
    size_t max_solution_size, const std::string &func_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param msg
 * @param num_vars
 * @param num_consts
 * @param max_solution_size
 * @param func_name
 */
void add_cegis_library(symbol_tablet &st, class goto_functionst &gf,
    class message_handlert &msg, size_t num_vars, size_t num_consts,
    size_t max_solution_size, const std::string &func_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 */
void add_cegis_execute_placeholder(symbol_tablet &st);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
code_typet cegis_execute_type();

#endif // CPROVER_CEGIS_INSTRUMENT_CEGIS_LIBRARY_H
