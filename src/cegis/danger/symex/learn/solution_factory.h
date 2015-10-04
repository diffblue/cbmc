/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_SOLUTION_FACTORY_H_
#define CEGIS_DANGER_SOLUTION_FACTORY_H_

#include <util/irep.h>

typedef std::map<const irep_idt, size_t> danger_variable_idst;

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
    const danger_variable_idst &ids, const size_t max_solution_size);

#endif /* CEGIS_DANGER_SOLUTION_FACTORY_H_ */
