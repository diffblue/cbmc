/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_LABELLED_ASSIGNMENTS_H
#define CPROVER_CEGIS_CEGIS_UTIL_LABELLED_ASSIGNMENTS_H

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

#endif // CPROVER_CEGIS_CEGIS_UTIL_LABELLED_ASSIGNMENTS_H
