/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_GENETIC_CONSTANT_STRATEGY_H
#define CPROVER_CEGIS_GENETIC_GENETIC_CONSTANT_STRATEGY_H

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_length
 */
size_t genetic_constant_strategy(class invariant_programt &program,
    size_t max_length);

#endif // CPROVER_CEGIS_GENETIC_GENETIC_CONSTANT_STRATEGY_H
