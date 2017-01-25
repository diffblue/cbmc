/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_PROCESSOR_TYPES_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_PROCESSOR_TYPES_H

#include <util/type.h>

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet cegis_opcode_type();

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet cegis_operand_type();

/**
 * @brief
 *
 * @details
 *
 * @return
 */
typet cegis_size_type();

/**
 * @brief
 *
 * @details
 *
 * @param type
 *
 * @return
 */
bool is_cegis_primitive(const typet &type);

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_PROCESSOR_TYPES_H
