/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_CONSTANT_WIDTH_H
#define CPROVER_CEGIS_CEGIS_UTIL_CONSTANT_WIDTH_H

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param expr
 * @param full_width
 *
 * @return
 */
size_t get_min_word_width(const class exprt &expr);

#endif // CPROVER_CEGIS_CEGIS_UTIL_CONSTANT_WIDTH_H
