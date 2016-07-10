/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DEFAULT_CONSTANT_STRATEGY_H_
#define CEGIS_DEFAULT_CONSTANT_STRATEGY_H_

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

#endif /* CEGIS_DEFAULT_CONSTANT_STRATEGY_H_ */
