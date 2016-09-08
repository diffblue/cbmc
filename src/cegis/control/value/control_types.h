/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_TYPES_H_
#define CEGIS_CONTROL_TYPES_H_

/**
 * @brief
 *
 * @details
 *
 * @param st
 *
 * @return
 */
const class symbol_typet &control_solution_type(const class symbol_tablet &st);

/**
 * @brief
 *
 * @details
 *
 * @param st
 *
 * @return
 */
const typet &control_float_value_type(const symbol_tablet &st);

/**
 * @brief
 *
 * @details
 *
 * @param st
 *
 * @return
 */
const typet &control_array_size_type(const symbol_tablet &st);

/**
 * @brief
 *
 * @details
 *
 * @param st
 *
 * @return
 */
const typet &control_runtime_array_size_type(const symbol_tablet &st);

#endif /* CEGIS_CONTROL_TYPES_H_ */
