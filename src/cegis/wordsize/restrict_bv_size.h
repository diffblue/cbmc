/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_WORDSIZE_RESTRICT_BV_SIZE_H_
#define CEGIS_WORDSIZE_RESTRICT_BV_SIZE_H_

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param width_in_bits
 */
void restrict_bv_size(class symbol_tablet &st, class goto_functionst &gf,
    size_t width_in_bits);

/**
 * @brief
 *
 * @details
 *
 * @param expr
 * @param width_in_bits
 */
void restrict_bv_size(class exprt &expr, size_t width_in_bits);

/**
 * @brief
 *
 * @details
 *
 * @param type
 * @param width_in_bits
 */
bool restrict_bv_size(class typet &type, size_t width_in_bits);

#endif /* CEGIS_WORDSIZE_RESTRICT_BV_SIZE_H_ */
