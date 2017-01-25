/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_LEARN_ADD_VARIABLE_REFS_H
#define CPROVER_CEGIS_DANGER_SYMEX_LEARN_ADD_VARIABLE_REFS_H

#include <cegis/invariant/symex/learn/instrument_vars.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param user_vars
 * @param max_solution_size
 */
void link_meta_variables(danger_programt &prog, const size_t user_vars,
    const size_t max_solution_size);

#endif // CPROVER_CEGIS_DANGER_SYMEX_LEARN_ADD_VARIABLE_REFS_H
