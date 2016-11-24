/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INVARIANT_ADD_INVARIANT_AND_TEMP_VARIABLES_H_
#define CEGIS_INVARIANT_ADD_INVARIANT_AND_TEMP_VARIABLES_H_

#include <functional>

typedef std::function<std::string(size_t)> inv_name_factoryt;

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_program_length
 * @param inv0_name
 * @param inv_name
 * @param inv_prime_name
 */
void add_invariant_variables(class invariant_programt &program,
    const std::string &inv0_name, const inv_name_factoryt inv_name,
    const inv_name_factoryt inv_prime_name);

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_program_length
 */
void create_tmp_variables(invariant_programt &program,
    const size_t max_program_length);

#endif /* CEGIS_INVARIANT_ADD_INVARIANT_AND_TEMP_VARIABLES_H_ */
