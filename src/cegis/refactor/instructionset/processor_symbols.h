/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_PROCESSOR_SYMBOLS_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_PROCESSOR_SYMBOLS_H

#include <util/std_expr.h>

/**
 * @brief
 *
 * @details
 */
#define CEGIS_PROC_PROGRAM_PARAM_ID "program"

/**
 * @brief
 *
 * @details
 */
#define CEGIS_PROC_PROGRAM_SIZE_PARAM_ID "size"

/**
 * @brief
 *
 * @details
 */
#define CEGIS_PROC_OPCODE_MEMBER_NAME "opcode"

/**
 * @brief
 *
 * @details
 */
#define CEGIS_PROC_INSTR_INDEX "i"

/**
 * @brief
 *
 * @details
 */
#define INSTR_TYPE_SUFFIX "_instructiont"

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param type
 */
std::string cegis_operand_array_name(
    const symbol_tablet &st,
    const typet &type);

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
 * @code
 * program[index].op_i
 * @endcode
 *
 * @param st
 * @param func_name
 * @param op
 *
 * @return
 */
member_exprt cegis_opcode(
    const symbol_tablet &st,
    const std::string &func_name);

/**
 * @brief
 *
 * @details
 * @code
 * program[index].op_i
 * @endcode
 *
 * @param st
 * @param func_name
 * @param op
 *
 * @return
 */
member_exprt cegis_operand_id(
    const symbol_tablet &st,
    const std::string &func_name,
    size_t op);

/**
 * @brief
 *
 * @details
 * @code
 * __CPROVER_cegis_variable_array_type[program[index].op_i]
 * @endcode
 *
 * @param st
 * @param func_name
 * @param type
 * @param op
 *
 * @return
 */
dereference_exprt cegis_operand(
    const symbol_tablet &st,
    const std::string &func_name,
    const typet &type,
    size_t op);

/**
 * @brief
 *
 * @details
 *
 * @param var
 *
 * @return
 */
bool is_refactor_meta_var(const irep_idt &var);

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_PROCESSOR_SYMBOLS_H
