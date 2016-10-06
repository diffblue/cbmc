/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_OPTIONS_REFACTORING_TYPE_H_
#define CEGIS_REFACTOR_OPTIONS_REFACTORING_TYPE_H_

typedef enum
{
  NULL_OBJECT
} refactoring_typet;

/**
 * @brief
 *
 * @details
 *
 * @param options
 *
 * @return
 */
refactoring_typet get_refactoring_type(const class optionst &options);

#endif /* CEGIS_REFACTOR_OPTIONS_REFACTORING_TYPE_H_ */
