/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_CONSTRAINT_CONSTRAINT_FACTORY_H_
#define CEGIS_REFACTOR_CONSTRAINT_CONSTRAINT_FACTORY_H_

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
void create_constraint_function_caller(class refactor_programt &prog);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
void link_refactoring_ranges(refactor_programt &prog);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
void create_refactoring_constraint(refactor_programt &prog);

#endif /* CEGIS_REFACTOR_CONSTRAINT_CONSTRAINT_FACTORY_H_ */
