/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_INSTRUMENT_VARIABLE_REFS_H_
#define CEGIS_DANGER_INSTRUMENT_VARIABLE_REFS_H_

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

#endif /* CEGIS_DANGER_INSTRUMENT_VARIABLE_REFS_H_ */
