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
 * int lhs_int;
 * int rhs_int;
 * int result_int;
 * double lhs_double;
 * double rhs_double;
 * double result_double;
 *
 * switch(instr_code)
 * {
 *   case 0:
 *   case 1:
 *     lhs_int=*__CPROVER_cegis_variable_array_int[op0];
 *     rhs_int=*__CPROVER_cegis_variable_array_int[op1];
 *     break;
 *   case 2:
 *   case 3:
 *     lhs_double=*__CPROVER_cegis_variable_array_double[op0];
 *     rhs_double=*__CPROVER_cegis_variable_array_double[op1];
 *     break;
 * }
 *
 * switch(instr_code)
 * {
 *   case 0:
 *     result_int=lhs_int + rhs_int;
 *     break;
 *   case 1:
 *     result_int=lhs_int - rhs_int;
 *     break;
 *   case 2:
 *     result_double=lhs_double + rhs_double;
 *     break;
 *   case 3:
 *     result_double=lhs_double - rhs_double;
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
