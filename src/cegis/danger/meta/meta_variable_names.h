/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_META_META_VARIABLE_NAMES_H
#define CPROVER_CEGIS_DANGER_META_META_VARIABLE_NAMES_H

#include <string>

/**
 * @brief
 *
 * @details
 *
 * @return
 */
std::string get_Dx0();

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 *
 * @return
 */
std::string get_Dx(const size_t loop_id);

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 *
 * @return
 */
std::string get_Dx_prime(const size_t loop_id);

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 * @param result_id
 *
 * @return
 */
std::string get_Rx(const size_t loop_id, const size_t result_id);

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 * @param result_id
 *
 * @return
 */
std::string get_Rx_prime(const size_t loop_id, const size_t result_id);

/**
 * @brief
 *
 * @details
 *
 * @param loop_id
 * @param result_id
 *
 * @return
 */
std::string get_Sx(const size_t loop_id, const size_t result_id);

#endif // CPROVER_CEGIS_DANGER_META_META_VARIABLE_NAMES_H
