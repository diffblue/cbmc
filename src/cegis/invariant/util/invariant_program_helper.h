/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_UTIL_INVARIANT_PROGRAM_HELPER_H
#define CPROVER_CEGIS_INVARIANT_UTIL_INVARIANT_PROGRAM_HELPER_H

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param body
 * @param target
 */
void erase_target(goto_programt::instructionst &body,
    const goto_programt::targett &target);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param width_in_bits
 */
void restrict_bv_size(class invariant_programt &prog, size_t width_in_bits);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param first_loop
 * @param last_loop
 * @param width_in_bits
 */
template<class loop_itert>
void restrict_bv_size(invariant_programt &prog, loop_itert first_loop,
    const loop_itert &last_loop, size_t width_in_bits);

#endif // CPROVER_CEGIS_INVARIANT_UTIL_INVARIANT_PROGRAM_HELPER_H
