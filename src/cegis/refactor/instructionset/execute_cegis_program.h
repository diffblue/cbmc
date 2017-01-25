/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_EXECUTE_CEGIS_PROGRAM_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_EXECUTE_CEGIS_PROGRAM_H

#include <goto-programs/goto_program.h>

#define CEGIS_REFACTOR_PROG_SUFFIX "_prog"

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param processor
 * @param program_name
 */
void declare_cegis_program(
    class symbol_tablet &st,
    class goto_functionst &gf,
    const std::string &processor,
    const std::string &program_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param processor
 *
 * @return
 */
std::string declare_cegis_program(
    symbol_tablet &st,
    goto_functionst &gf,
    const std::string &processor);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param instr
 * @param processor
 * @param program_name
 */
void call_processor(
    const symbol_tablet &st,
    goto_programt::instructiont &instr,
    const std::string &processor,
    const std::string &program_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param processor
 * @param program_name
 *
 * @return
 */
goto_programt::targett call_processor(
    const symbol_tablet &st,
    goto_programt &body,
    goto_programt::targett pos,
    const std::string &processor,
    const std::string &program_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param size
 */
void set_cegis_processor_sizes(symbol_tablet &st, size_t size);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param first
 * @param last
 * @param size
 */
void set_cegis_processor_sizes(
    const symbol_tablet &st,
    goto_programt::targett first,
    goto_programt::const_targett last,
    size_t size);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param instr
 * @param index
 * @param var_name
 */
void instrument_cegis_operand(
    const symbol_tablet &st,
    goto_programt::instructiont &instr,
    size_t index,
    const irep_idt &var_name);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param body
 * @param pos
 * @param index
 * @param var_name
 */
goto_programt::targett instrument_cegis_operand(
    const symbol_tablet &st,
    goto_programt &body,
    goto_programt::targett pos,
    size_t index,
    const irep_idt &var_name);

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_EXECUTE_CEGIS_PROGRAM_H
