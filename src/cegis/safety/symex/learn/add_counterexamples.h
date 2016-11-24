/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_LEARN_ADD_COUNTEREXAMPLES_H_
#define CEGIS_SAFETY_LEARN_ADD_COUNTEREXAMPLES_H_

#include <cegis/invariant/symex/learn/add_counterexamples.h>
#include <cegis/safety/value/safety_goto_ce.h>

typedef std::deque<safety_goto_cet> safety_goto_cest;

/**
 * @brief
 *
 * @details
 */
#define X0_CHOICE_PREFIX CEGIS_PREFIX "x0_choice_"

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ces
 * @param use_x0_ce
 */
void safety_add_learned_counterexamples(class safety_programt &prog,
    const safety_goto_cest &ces, constraint_factoryt constraint);

#endif /* CEGIS_SAFETY_LEARN_ADD_COUNTEREXAMPLES_H_ */
