/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_CONSTANT_STRATEGY_H_
#define CEGIS_DANGER_CONSTANT_STRATEGY_H_

#include <cstddef>

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
typedef size_t (*constant_strategyt)(class danger_programt &program,
    const size_t max_length);

#endif /* CEGIS_DANGER_CONSTANT_STRATEGY_H_ */
