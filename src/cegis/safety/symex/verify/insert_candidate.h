/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_SYMEX_VERIFY_INSERT_CANDIDATE_H
#define CPROVER_CEGIS_SAFETY_SYMEX_VERIFY_INSERT_CANDIDATE_H

#include <cegis/safety/value/safety_goto_solution.h>

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param canddiate
 */
void safety_insert_candidate(class safety_programt &program,
    const safety_goto_solutiont &candidate);

#endif // CPROVER_CEGIS_SAFETY_SYMEX_VERIFY_INSERT_CANDIDATE_H
