/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CEGIS_PROCESSOR_BODY_FACTORY_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CEGIS_PROCESSOR_BODY_FACTORY_H

#include <cegis/refactor/instructionset/operand_data.h>

/**
 * @brief
 *
 * @details
 *
 * @param op
 *
 * @return
 */
std::string cegis_operand_base_name(size_t op);

/**
 * @brief
 *
 * @details
 *
 * @param slots
 *
 * @return
 */
size_t cegis_max_operands(const cegis_operand_datat &slots);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param name
 * @param slots
 */
void generate_processor_body(
    class symbol_tablet &st,
    class goto_programt &body,
    const std::string &name,
    const cegis_operand_datat &slots);

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CEGIS_PROCESSOR_BODY_FACTORY_H
