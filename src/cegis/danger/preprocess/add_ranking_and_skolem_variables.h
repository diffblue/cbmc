/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_ADD_INVARIANT_AND_TEMP_VARIABLES_H_
#define CEGIS_DANGER_ADD_INVARIANT_AND_TEMP_VARIABLES_H_

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_program_length
 */
void add_ranking_and_skolem_variables(class danger_programt &program,
    const size_t max_program_length);

#endif /* CEGIS_DANGER_ADD_INVARIANT_AND_TEMP_VARIABLES_H_ */
