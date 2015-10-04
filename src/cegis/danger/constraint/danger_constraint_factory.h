/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_CONSTRAINT_FACTORY_H_
#define CEGIS_DANGER_CONSTRAINT_FACTORY_H_

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param number_of_loops
 *
 * @return
 */
exprt create_danger_constraint(const size_t number_of_loops);

/**
 * @brief
 *
 * @details
 *
 * @param base_name
 *
 * @return
 */
notequal_exprt danger_component_as_bool(const std::string &base_name);

#endif /* CEGIS_DANGER_CONSTRAINT_FACTORY_H_ */
