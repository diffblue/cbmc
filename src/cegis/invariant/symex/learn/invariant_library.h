/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INVARIANT_LIBRARY_H_
#define CEGIS_INVARIANT_LIBRARY_H_

#include <cstddef>

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
std::string get_invariant_library_text(size_t num_vars, size_t num_consts,
    size_t max_solution_size, const std::string &func_name);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param msg
 * @param num_vars
 * @param num_consts
 * @param max_solution_size
 * @param func_name
 */
void add_invariant_library(class invariant_programt &prog,
    class message_handlert &msg, size_t num_vars, size_t num_consts,
    size_t max_solution_size, const std::string &func_name);

#endif /* CEGIS_INVARIANT_LIBRARY_H_ */
