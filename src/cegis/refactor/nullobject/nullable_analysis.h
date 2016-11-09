/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_NULLOBJECT_NULLABLE_ANALYSIS_H_
#define CEGIS_REFACTOR_NULLOBJECT_NULLABLE_ANALYSIS_H_

#include <cegis/refactor/instructionset/operand_data.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 *
 * @return
 */
std::set<irep_idt> get_nullable_methods(const class refactor_programt &prog);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param state_vars
 *
 * @return
 */
std::map<typet, size_t> slots_per_type(const symbol_tablet &st,
    const std::set<irep_idt> &state_vars);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param method
 *
 * @return
 */
cegis_operand_datat get_operand_signature(
    const symbol_tablet &st,
    const irep_idt &method);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param first
 * @param last
 * @param method
 * @param processor
 * @param prog
 */
void replace_method_call_by_processor(
    const symbol_tablet &st,
    goto_programt &body,
    goto_programt::targett first,
    goto_programt::targett last,
    const irep_idt &method,
    const std::string &processor,
    const std::string &prog);

#endif /* CEGIS_REFACTOR_NULLOBJECT_NULLABLE_ANALYSIS_H_ */
