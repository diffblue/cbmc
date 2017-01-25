/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_SYMEX_LEARN_SOLUTION_FACTORY_H
#define CPROVER_CEGIS_SAFETY_SYMEX_LEARN_SOLUTION_FACTORY_H

#include <cegis/safety/value/safety_goto_solution.h>

typedef std::map<const irep_idt, size_t> operand_variable_idst;

/**
 * @brief
 *
 * @details
 *
 * @param solution
 * @param prog
 * @param trace
 * @param var_ids
 * @param max_solution_size
 */
void create_safety_solution(safety_goto_solutiont &solution,
    const class safety_programt &prog, const class goto_tracet &trace,
    const operand_variable_idst &var_ids, size_t max_solution_size);

/**
 * @brief
 *
 * @details
 *
 * @param solution
 * @param st
 * @param gf
 * @param ind
 * @param var_ids
 */
void create_safety_solution(safety_goto_solutiont &solution,
    const symbol_tablet &st, const class goto_functionst &gf,
    const class program_individualt &ind,
    const operand_variable_idst &var_ids);

/**
 * @brief
 *
 * @details
 *
 * @param solution
 * @param st
 * @param gf
 * @param ind
 * @param var_ids
 * @param info_fac
 */
void create_safety_solution(safety_goto_solutiont &solution,
    const symbol_tablet &st, const class goto_functionst &gf,
    const program_individualt &ind,
    const operand_variable_idst &var_ids,
    class instruction_set_info_factoryt &info_fac);

#endif // CPROVER_CEGIS_SAFETY_SYMEX_LEARN_SOLUTION_FACTORY_H
