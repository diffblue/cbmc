/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_TYPES_H_
#define CEGIS_JSA_TYPES_H_

#include <util/std_types.h>

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet jsa_word_type();

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet jsa_internal_index_type();

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet jsa_iterator_id_type();

/**
 * @brief
 *
 * @details
 *
 * @return
 */
symbol_typet jsa_predicate_instruction_type();

/**
 * @brief
 *
 * @details
 *
 * @param size
 *
 * @return
 */
array_typet jsa_predicate_type(const exprt &size);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
symbol_typet jsa_invariant_instruction_type();

/**
 * @brief
 *
 * @details
 *
 * @param size
 *
 * @return
 */
array_typet jsa_invariant_type(const exprt & size);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
symbol_typet jsa_query_instruction_type();

/**
 * @brief
 *
 * @details
 *
 * @param size
 *
 * @return
 */
array_typet jsa_query_type(const exprt & size);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
symbol_typet jsa_heap_type();

#endif /* CEGIS_JSA_TYPES_H_ */
