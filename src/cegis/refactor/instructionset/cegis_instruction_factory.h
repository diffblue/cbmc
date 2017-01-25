/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CEGIS_INSTRUCTION_FACTORY_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CEGIS_INSTRUCTION_FACTORY_H

#include <cegis/refactor/instructionset/operand_data.h>
#include <cegis/refactor/instructionset/instruction_description.h>

typedef std::map<instruction_descriptiont::typest, instruction_descriptionst> ordered_instructionst;

/**
 * @brief
 *
 * @details
 *
 * @param signature
 *
 * @return
 */
ordered_instructionst get_instructions_for_types(
    const cegis_operand_datat &signature);

/**
 * @brief
 *
 * @details
 *
 * @param instrs
 *
 * @result
 */
instruction_descriptionst::size_type num_instrs(
    const ordered_instructionst &instrs);

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CEGIS_INSTRUCTION_FACTORY_H
