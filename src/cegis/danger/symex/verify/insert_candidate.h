/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_INSERT_CANDIDATE_H_
#define CEGIS_DANGER_INSERT_CANDIDATE_H_

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
void danger_insert_candidate(danger_programt &program,
    const candidatet &candidate);

#endif /* CEGIS_DANGER_INSERT_CANDIDATE_H_ */
