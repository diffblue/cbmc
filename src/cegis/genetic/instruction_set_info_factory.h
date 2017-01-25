/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_INSTRUCTION_SET_INFO_FACTORY_H
#define CPROVER_CEGIS_GENETIC_INSTRUCTION_SET_INFO_FACTORY_H

#include <functional>

#include <goto-programs/goto_program.h>

typedef std::map<size_t, goto_programt::instructionst> instruction_sett;
typedef std::map<size_t, size_t> instruction_set_infot;

/**
 * @brief
 *
 * @details
 */
class instruction_set_info_factoryt
{
  std::function<const class goto_programt &()> body_provider;
  instruction_sett instructions;
  instruction_set_infot info;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param body
   */
  explicit instruction_set_info_factoryt(const goto_programt &body);

  /**
   * @brief
   *
   * @details
   *
   * @param provider
   * @tparam goto_program_providert
   */
  template<class goto_program_providert>
  instruction_set_info_factoryt(const goto_program_providert &provider);

  /**
   * @brief
   *
   * @details
   */
  ~instruction_set_info_factoryt();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const instruction_sett &get_instructions();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const instruction_set_infot &get_info();
};

#include "instruction_set_info_factory.inc"

#endif // CPROVER_CEGIS_GENETIC_INSTRUCTION_SET_INFO_FACTORY_H
