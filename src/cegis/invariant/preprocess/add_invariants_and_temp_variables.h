/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_PREPROCESS_ADD_INVARIANTS_AND_TEMP_VARIABLES_H
#define CPROVER_CEGIS_INVARIANT_PREPROCESS_ADD_INVARIANTS_AND_TEMP_VARIABLES_H

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
 * @param inv0_name
 * @param inv_name
 * @param inv_prime_name
 * @param type
 */
void add_invariant_variables(class invariant_programt &program,
    const std::string &inv0_name, const inv_name_factoryt inv_name,
    const inv_name_factoryt inv_prime_name, const class typet &type);

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

/**
 * @brief
 *
 * @details
 *
 * @param program
 * @param max_program_length
 * @param type
 */
void create_tmp_variables(
    invariant_programt &program,
    const size_t max_program_length,
    const class typet &type);

#endif // CPROVER_CEGIS_INVARIANT_PREPROCESS_ADD_INVARIANTS_AND_TEMP_VARIABLES_H
