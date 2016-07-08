/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_INSERT_PREDICATES_AND_QUERIES_H_
#define CEGIS_JSA_INSERT_PREDICATES_AND_QUERIES_H_

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param max_size
 */
void declare_jsa_predicates(class jsa_programt &prog, size_t max_size);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param max_size
 */
void declare_jsa_query(jsa_programt &prog, size_t max_size);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param max_size
 */
void declare_jsa_invariant(jsa_programt &prog, size_t max_size);

#endif /* CEGIS_JSA_INSERT_PREDICATES_AND_QUERIES_H_ */
