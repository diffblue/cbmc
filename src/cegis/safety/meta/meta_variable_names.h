/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_META_META_VARIABLE_NAMES_H
#define CPROVER_CEGIS_SAFETY_META_META_VARIABLE_NAMES_H

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

#endif // CPROVER_CEGIS_SAFETY_META_META_VARIABLE_NAMES_H
