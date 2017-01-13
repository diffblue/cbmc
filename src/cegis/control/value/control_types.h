/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_VALUE_CONTROL_TYPES_H
#define CPROVER_CEGIS_CONTROL_VALUE_CONTROL_TYPES_H

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
const class symbol_typet &control_vector_solution_type(const class symbol_tablet &st);

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

#endif // CPROVER_CEGIS_CONTROL_VALUE_CONTROL_TYPES_H
