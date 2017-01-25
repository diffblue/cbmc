/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_CONSTRAINT_SAFETY_CONSTRAINT_FACTORY_H
#define CPROVER_CEGIS_SAFETY_CONSTRAINT_SAFETY_CONSTRAINT_FACTORY_H

#include <util/expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param number_of_loops
 *
 * @return
 */
exprt create_safety_constraint(const size_t number_of_loops);

#endif // CPROVER_CEGIS_SAFETY_CONSTRAINT_SAFETY_CONSTRAINT_FACTORY_H
