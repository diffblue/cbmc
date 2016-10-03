/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_VALUE_REFACTOR_COUNTERXAMPLE_H_
#define CEGIS_REFACTOR_VALUE_REFACTOR_COUNTERXAMPLE_H_

#include <deque>
#include <map>

#include <util/expr.h>

/**
 * @brief
 *
 * @details List of values per CE location.
 */
typedef std::map<const irep_idt, exprt::operandst> refactor_counterexamplet;

typedef std::deque<refactor_counterexamplet> refactor_counterexamplest;

#endif /* CEGIS_REFACTOR_VALUE_REFACTOR_COUNTERXAMPLE_H_ */
