/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_OPTIONS_REFACTORING_TYPE_H
#define CPROVER_CEGIS_REFACTOR_OPTIONS_REFACTORING_TYPE_H

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

#endif // CPROVER_CEGIS_REFACTOR_OPTIONS_REFACTORING_TYPE_H
