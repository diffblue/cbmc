/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_CONSTRAINT_FACTORY_H_
#define CEGIS_SAFETY_CONSTRAINT_FACTORY_H_

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

#endif /* CEGIS_SAFETY_CONSTRAINT_FACTORY_H_ */
