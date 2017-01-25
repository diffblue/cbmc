/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H

#include <set>

#include <util/type.h>
#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/goto_range.h>

/**
 * @brief
 *
 * @details
 *
 * @param range
 *
 * @return
 */
std::set<typet> collect_context_types(const goto_ranget &range);

/**
 * @brief
 *
 * @details
 * @code
 * execute_next_instr:
 * #define program[i].opcode opcode
 * #define program[i].op0 op0
 * #define program[i].op1 op1
 * #define program[i].op2 op2
 *
 * if (instr_code < 2)
 * {
 *   __CPROVER_assume(op0 < __CPROVER_cegis_variable_array_int_size);
 *   __CPROVER_assume(op1 < __CPROVER_cegis_variable_array_int_size);
 *   __CPROVER_assume(op2 < __CPROVER_cegis_variable_array_int_size);
 * } else if (instr_code < 4)
 * {
 *   __CPROVER_assume(op0 < __CPROVER_cegis_variable_array_double_size);
 *   __CPROVER_assume(op1 < __CPROVER_cegis_variable_array_double_size);
 *   __CPROVER_assume(op2 < __CPROVER_cegis_variable_array_double_size);
 * } else if (instr_code < 5)
 * {
 *   __CPROVER_assume(op0 < __CPROVER_cegis_variable_array_iobject_size);
 *   __CPROVER_assume(op1 < __CPROVER_cegis_variable_array_double_size);
 * }
 *
 * switch(instr_code)
 * {
 *   case 0:
 *     *__CPROVER_cegis_variable_array_int[op0]=*__CPROVER_cegis_variable_array_int[op1] + *__CPROVER_cegis_variable_array_int[op2];
 *     break;
 *   case 1:
 *     *__CPROVER_cegis_variable_array_int[op0]=*__CPROVER_cegis_variable_array_int[op1] - *__CPROVER_cegis_variable_array_int[op2];
 *     break;
 *   case 2:
 *     *__CPROVER_cegis_variable_array_double[op0]=*__CPROVER_cegis_variable_array_double[op1] + *__CPROVER_cegis_variable_array_double[op2];
 *     break;
 *   case 3:
 *     *__CPROVER_cegis_variable_array_double[op0]=*__CPROVER_cegis_variable_array_double[op1] - *__CPROVER_cegis_variable_array_double[op2];
 *     break;
 *   case 4:
 *     *__CPROVER_cegis_variable_array_double[op0]=(*__CPROVER_cegis_variable_array_iobject[op1]).someMethod(*__CPROVER_cegis_variable_array_int[op2]);
 *     break;
 *   case 5:
 *     (*__CPROVER_cegis_variable_array_iobject[op0]).someOtherMethod(*__CPROVER_cegis_variable_array_double[op1]);
 *     break;
 * }
 * @endcode
 *
 * @param st
 * @param gf
 * @param variable_slots_per_context_type
 *
 * @return
 */
std::string create_cegis_processor(
    symbol_tablet &st,
    class goto_functionst &gf,
    const std::map<typet, size_t> &variable_slots_per_context_type);

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H
