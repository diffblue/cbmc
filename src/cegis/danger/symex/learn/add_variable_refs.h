/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_INSTRUMENT_VARIABLE_REFS_H_
#define CEGIS_DANGER_INSTRUMENT_VARIABLE_REFS_H_

#include <util/irep.h>

typedef std::map<const irep_idt, size_t> danger_variable_idst;

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param ids
 * @param max_solution_size
 *
 * @return
 */
void danger_add_variable_refs(class danger_programt &prog,
    const danger_variable_idst &ids, const size_t max_solution_size);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @params ids
 *
 * @return
 */
size_t get_danger_variable_ids(const class symbol_tablet &st,
    danger_variable_idst &ids);

#endif /* CEGIS_DANGER_INSTRUMENT_VARIABLE_REFS_H_ */
