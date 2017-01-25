/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_VERIFY_INSERT_CANDIDATE_H
#define CPROVER_CEGIS_DANGER_SYMEX_VERIFY_INSERT_CANDIDATE_H

/**
 * @brief Candidate solution type for this CEGIS component.
 *
 * @details Solutions are provided as a set of GOTO function bodies
 * (goto_programt::instructionst) for function names.
 */
typedef class danger_goto_solutiont candidatet;

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param candidate
 */
void danger_insert_candidate(class danger_programt &program,
    const candidatet &candidate);

#endif // CPROVER_CEGIS_DANGER_SYMEX_VERIFY_INSERT_CANDIDATE_H
