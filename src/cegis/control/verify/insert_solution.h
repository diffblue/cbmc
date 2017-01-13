/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/


#ifndef CPROVER_CEGIS_CONTROL_VERIFY_INSERT_SOLUTION_H
#define CPROVER_CEGIS_CONTROL_VERIFY_INSERT_SOLUTION_H

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param solution
 */
void insert_solution(
    class control_programt &program,
    const class control_solutiont &solution);

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param solution
 */
void insert_solution(
    class control_programt &program,
    const class control_vector_solutiont &solution);


#endif // CPROVER_CEGIS_CONTROL_VERIFY_INSERT_SOLUTION_H
