/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_PREPROCESSING_CREATE_TEMP_VARIABLES_H
#define CPROVER_CEGIS_JSA_PREPROCESSING_CREATE_TEMP_VARIABLES_H

#include <cstddef>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param max_size
 */
void create_jsa_temp_variables(class jsa_programt &prog, size_t max_size);

#endif // CPROVER_CEGIS_JSA_PREPROCESSING_CREATE_TEMP_VARIABLES_H
