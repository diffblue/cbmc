/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_EXTRACT_COUNTEREXAMPLE_H_
#define CEGIS_DANGER_EXTRACT_COUNTEREXAMPLE_H_

#include <util/std_expr.h>

/**
 * @brief Counterexample type for this CEGIS component.
 *
 * @details Counterexamples give a set of values used for the state variables.
 */
typedef std::map<const irep_idt, exprt> counterexamplet;

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param trace
 * @param quantifiers
 */
void danger_extract_counterexample(counterexamplet &result,
    const class goto_tracet &trace, const goto_programt::targetst &quantifiers);

#endif /* CEGIS_DANGER_EXTRACT_COUNTEREXAMPLE_H_ */
