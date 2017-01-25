/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_VERIFY_RESTRICT_COUNTEREXAMPLES_H
#define CPROVER_CEGIS_DANGER_SYMEX_VERIFY_RESTRICT_COUNTEREXAMPLES_H

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param num_loops
 */
void force_assertion_satisfaction(class goto_functionst &gf,
    const size_t num_loops);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param num_loop
 */
void force_assertion_violation(goto_functionst &gf, const size_t num_loops);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param loop_guards
 */
void force_loop_exit(goto_functionst &gf, const exprt::operandst &loop_guards);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param num_loops
 */
void force_guard_violation(goto_functionst &gf, const size_t num_loops);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param num_loops
 */
void force_ranking_error(goto_functionst &gf,
    const size_t num_loops);

#endif // CPROVER_CEGIS_DANGER_SYMEX_VERIFY_RESTRICT_COUNTEREXAMPLES_H
