/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_CONSTANT_LITERALS_CONSTANT_STRATEGY_H
#define CPROVER_CEGIS_INVARIANT_CONSTANT_LITERALS_CONSTANT_STRATEGY_H

#include <cstddef>

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 *
 * @param program
 *
 * @return
 */
std::vector<constant_exprt> collect_literal_constants(
    const class invariant_programt &program);

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_length
 *
 * @return
 */
size_t literals_constant_strategy(invariant_programt &program,
    const size_t max_length);

#endif // CPROVER_CEGIS_INVARIANT_CONSTANT_LITERALS_CONSTANT_STRATEGY_H
