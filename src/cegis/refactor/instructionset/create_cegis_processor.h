/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H_
#define CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H_

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
 * @code
 * execute_next_instr:
 * int opcode=program[i].opcode;
 * int op0=program[i].op0;
 * int op1=program[i].op1;
 * int result_op=program[i].result_op;
 *
 * int op0_int;
 * int op1_int;
 * int result_int;
 * double op0_double;
 * double op1_double;
 * double result_double;
 * IObject op0_iobject;
 * IObject op1_iobject;
 *
 * switch(instr_code)
 * {
 *   case 0:
 *   case 1:
 *     op0_int=*__CPROVER_cegis_variable_array_int[op0];
 *     op1_int=*__CPROVER_cegis_variable_array_int[op1];
 *     break;
 *   case 2:
 *   case 3:
 *     op0_double=*__CPROVER_cegis_variable_array_double[op0];
 *     op1_double=*__CPROVER_cegis_variable_array_double[op1];
 *     break;
 *   case 4:
 *     op0_iobject=*__CPROVER_cegis_variable_array_iobject[op0];
 *     op1_int=*__CPROVER_cegis_variable_array_int[op1];
 *   case 5:
 *     op0_iobject=*__CPROVER_cegis_variable_array_iobject[op0];
 *     op1_double=*__CPROVER_cegis_variable_array_double[op1];
 *     break;
 * }
 *
 * switch(instr_code)
 * {
 *   case 0:
 *     result_int=op0_int + op1_int;
 *     break;
 *   case 1:
 *     result_int=op0_int - op1_int;
 *     break;
 *   case 2:
 *     result_double=op0_double + op1_double;
 *     break;
 *   case 3:
 *     result_double=op0_double - op1_double;
 *     break;
 *   case 4:
 *     result_double=op0_iobject.someMethod(op1_int);
 *     break;
 *   case 5:
 *     op0_iobject.someOtherMethod(op1_double);
 *     break;
 * }
 *
 * switch(instr_code)
 * {
 *   case 0:
 *   case 1:
 *     *__CPROVER_cegis_variable_array_int[rop]=result_int;
 *     break;
 *   case 2:
 *   case 3:
 *     *__CPROVER_cegis_variable_array_double[rop]=result_double;
 *     break;
 *   case 4:
 *     *__CPROVER_cegis_variable_array_double[rop]=result_double;
 *     break;
 *   case 5:
 *     // void method
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

#endif /* CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H_ */
