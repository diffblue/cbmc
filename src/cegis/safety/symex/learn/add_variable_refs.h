#ifndef CEGIS_SAFETY_ADD_VARIABLE_REFS_H_
#define CEGIS_SAFETY_ADD_VARIABLE_REFS_H_

#include <util/irep.h>

typedef std::map<const irep_idt, size_t> invariant_variable_idst;

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param var_ids
 * @parma max_solution_size
 */
void add_safety_learning_variable_refs(class invariant_programt &prog,
    const invariant_variable_idst &var_ids, size_t max_solution_size);

#endif /* CEGIS_SAFETY_ADD_VARIABLE_REFS_H_ */
