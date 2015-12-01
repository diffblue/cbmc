/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_LITERALS_CONSTANT_STRATEGY_H_
#define CEGIS_DANGER_LITERALS_CONSTANT_STRATEGY_H_

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
    const class danger_programt &program);

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
size_t literals_constant_strategy(danger_programt &program,
    const size_t max_length);

#endif /* CEGIS_DANGER_LITERALS_CONSTANT_STRATEGY_H_ */
