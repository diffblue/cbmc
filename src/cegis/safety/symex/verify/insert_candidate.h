/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_SYMEX_VERIFY_INSERT_CANDIDATE_H_
#define CEGIS_SAFETY_SYMEX_VERIFY_INSERT_CANDIDATE_H_

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

#endif /* CEGIS_SAFETY_SYMEX_VERIFY_INSERT_CANDIDATE_H_ */
