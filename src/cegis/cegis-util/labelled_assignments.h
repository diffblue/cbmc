/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_UTIL_LABELLED_ASSIGNMENTS_H_
#define CEGIS_UTIL_LABELLED_ASSIGNMENTS_H_

#include <deque>

#include <util/expr.h>

/**
 * @brief
 *
 * @details
 */
typedef std::map<const irep_idt, exprt::operandst> labelled_assignmentst;

/**
 * @brief
 *
 * @details
 */
typedef std::deque<labelled_assignmentst> labelled_counterexamplest;

#endif /* CEGIS_UTIL_LABELLED_ASSIGNMENTS_H_ */
