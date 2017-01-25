/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_CONSTANT_CONSTANT_STRATEGY_H
#define CPROVER_CEGIS_INVARIANT_CONSTANT_CONSTANT_STRATEGY_H

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
typedef size_t (*constant_strategyt)(class invariant_programt &program,
    const size_t max_length);

#endif // CPROVER_CEGIS_INVARIANT_CONSTANT_CONSTANT_STRATEGY_H
