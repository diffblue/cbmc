/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_RESTRICT_COUNTEREXAMPLES_H_
#define CEGIS_DANGER_RESTRICT_COUNTEREXAMPLES_H_

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param prog
 */
void force_assertion_satisfaction(class goto_functionst &gf,
    const size_t num_loops);

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param prog
 */
void force_invariant_and_guard_satisfaction(class goto_functionst &gf,
    const size_t num_loops);

#endif /* CEGIS_DANGER_RESTRICT_COUNTEREXAMPLES_H_ */
