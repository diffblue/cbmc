/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_PREPROCESS_ADD_RANKING_AND_SKOLEM_VARIABLES_H
#define CPROVER_CEGIS_DANGER_PREPROCESS_ADD_RANKING_AND_SKOLEM_VARIABLES_H

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

#endif // CPROVER_CEGIS_DANGER_PREPROCESS_ADD_RANKING_AND_SKOLEM_VARIABLES_H
