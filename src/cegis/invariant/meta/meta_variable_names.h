/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INVARIANT_META_VARIABLE_NAMES_H_
#define CEGIS_INVARIANT_META_VARIABLE_NAMES_H_

#include <string>

#define DANGER_CE_QUANTIFIER_LABEL_PREFIX "__CPROVER_danger_ceq_"

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
 * @param id
 *
 * @return
 */
std::string get_tmp(const size_t id);

#endif /* CEGIS_INVARIANT_META_VARIABLE_NAMES_H_ */
