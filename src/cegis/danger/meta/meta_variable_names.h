/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_META_VARIABLE_NAMES_H_
#define CEGIS_DANGER_META_VARIABLE_NAMES_H_

#include <string>

/**
 * @brief
 *
 * @details
 *
 * @return
 */
std::string get_Ax();

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
 *
 * @return
 */
std::string get_Gx(const size_t loop_id);

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

/**
 * @brief
 *
 * @details
 *
 * @param id
 *
 * @return
 */
std::string get_tmp(const size_t id);

#endif /* CEGIS_DANGER_META_VARIABLE_NAMES_H_ */
