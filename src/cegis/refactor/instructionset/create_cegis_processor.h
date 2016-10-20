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
