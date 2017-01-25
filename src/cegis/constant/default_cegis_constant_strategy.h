/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONSTANT_DEFAULT_CEGIS_CONSTANT_STRATEGY_H
#define CPROVER_CEGIS_CONSTANT_DEFAULT_CEGIS_CONSTANT_STRATEGY_H

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_length
 */
size_t default_cegis_constant_strategy(
    class symbol_tablet &st,
    class goto_functionst &gf);

#endif // CPROVER_CEGIS_CONSTANT_DEFAULT_CEGIS_CONSTANT_STRATEGY_H
