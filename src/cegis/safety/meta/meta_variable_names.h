/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_META_VARIABLE_NAMES_H_
#define CEGIS_SAFETY_META_VARIABLE_NAMES_H_

#include <string>

/**
 * @brief
 *
 * @details
 *
 * @return
 */
std::string get_Ix0();

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 *
 * @return
 */
std::string get_Ix(const size_t loop_id);

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 *
 * @return
 */
std::string get_Ix_prime(const size_t loop_id);

#endif /* CEGIS_DANGER_META_VARIABLE_NAMES_H_ */
