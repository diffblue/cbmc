/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_INSTRUCTION_DESCRIPTION_H
#define CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_INSTRUCTION_DESCRIPTION_H

#include <functional>

#include <goto-programs/goto_program.h>

typedef std::function<
    goto_programt::targett(
        const symbol_tablet &,
        std::string,
        goto_programt &,
        goto_programt::targett)> instruction_factoryt;

/**
 * @brief
 *
 * @details
 */
class instruction_descriptiont {
public:
  typedef std::vector<typet> typest;
  const typest signature;
private:
  const instruction_factoryt factory;
public:
  /**
   * @brief
   *
   * @detais
   *
   * @param signature
   * @param factory
   */
  instruction_descriptiont(
      const typest &signature,
      const instruction_factoryt &factory);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  bool has_result() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const typet &result_type() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  typest operand_types() const;

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param func_name
   * @param body
   * @param pos
   *
   * @return
   */
  goto_programt::targett operator()(
      const symbol_tablet &st,
      const std::string &func_name,
      goto_programt &body,
      goto_programt::targett pos) const;
};

/**
 * @brief
 *
 * @details
 */
typedef std::vector<instruction_descriptiont> instruction_descriptionst;

#endif // CPROVER_CEGIS_REFACTOR_INSTRUCTIONSET_INSTRUCTION_DESCRIPTION_H
