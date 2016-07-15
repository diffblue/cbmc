/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DEFAULT_JSA_CONSTANT_STRATEGY_H_
#define CEGIS_DEFAULT_JSA_CONSTANT_STRATEGY_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 */
goto_programt::targett default_jsa_constant_strategy(
    class symbol_tablet &st,
    class goto_functionst &gf);

#endif /* CEGIS_DEFAULT_JSA_CONSTANT_STRATEGY_H_ */
