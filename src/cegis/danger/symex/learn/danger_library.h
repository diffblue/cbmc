/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_LIBRARY_H_
#define CEGIS_DANGER_LIBRARY_H_

#include <cstddef>

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
 */
void add_danger_library(class danger_programt &prog,
    class message_handlert &msg, const size_t num_vars, const size_t num_consts,
    const size_t max_solution_size);

#endif /* CEGIS_DANGER_LIBRARY_H_ */
