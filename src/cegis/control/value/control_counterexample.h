/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_COUNTEREXAMPLE_H_
#define CEGIS_CONTROL_COUNTEREXAMPLE_H_

#include <deque>
#include <map>

#include <util/expr.h>

/**
 * @brief
 *
 * @details List of values per CE location.
 */
typedef std::map<const irep_idt, exprt::operandst> control_counterexamplet;

typedef std::deque<control_counterexamplet> control_counterexamplest;

#endif /* CEGIS_CONTROL_COUNTEREXAMPLE_H_ */
