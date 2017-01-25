/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_PREPROCESSING_DEFAULT_JSA_CONSTANT_STRATEGY_H
#define CPROVER_CEGIS_JSA_PREPROCESSING_DEFAULT_JSA_CONSTANT_STRATEGY_H

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

#endif // CPROVER_CEGIS_JSA_PREPROCESSING_DEFAULT_JSA_CONSTANT_STRATEGY_H
