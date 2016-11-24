/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_SOLUTION_FACTORY_H_
#define CEGIS_DANGER_SOLUTION_FACTORY_H_

#include <goto-programs/goto_program.h>

#include <cegis/value/program_individual.h>

typedef std::map<size_t, goto_programt::instructionst> instruction_sett;
typedef std::map<const irep_idt, size_t> invariant_variable_idst;

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param trace
 * @param ids
 * @param max_solution_size
 *
 * @return
 */
void create_danger_solution(class danger_goto_solutiont &result,
    const class danger_programt &prog, const class goto_tracet &trace,
    const invariant_variable_idst &ids, const size_t max_solution_size);

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param ind
 * @param instr
 * @param ids
 */
void create_danger_solution(danger_goto_solutiont &result,
    const danger_programt &prog, const program_individualt &ind,
    const instruction_sett &instr, const invariant_variable_idst &ids);

/**
 * @brief
 *
 * @details
 *
 * @param result
 * @param prog
 * @param ind
 * @param ids
 */
void create_danger_solution(danger_goto_solutiont &result,
    const danger_programt &prog, const program_individualt &ind,
    const invariant_variable_idst &ids);

#endif /* CEGIS_DANGER_SOLUTION_FACTORY_H_ */
