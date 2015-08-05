/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SYMEX_LEARNING_PROGRAM_ADAPTERT_H_
#define CEGIS_SYMEX_LEARNING_PROGRAM_ADAPTERT_H_

#include <deque>
#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details
 */
class symex_learning_program_adaptert
{
public:
  /**
   * @brief Counterexample type for this CEGIS component.
   *
   * @details Counterexamples give a set of assignments (variable names and
   * corresponding assignments) for which the previous solution violates the
   * safety property.
   */
  typedef std::map<const irep_idt, exprt> counterexamplet;
private:
  symbol_tablet symbol_table;
  goto_functionst gf;
  const class cegis_optionst &options;
  class ui_message_handlert &msg;
  const std::deque<counterexamplet> &counterexamples;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param symbol_table
   * @param goto_functions
   * @param options
   * @param msg
   * @param counterexamples
   */
  symex_learning_program_adaptert(const symbol_tablet &symbol_table,
      const goto_functionst &goto_functions, const cegis_optionst &options,
      ui_message_handlert &msg,
      const std::deque<counterexamplet> &counterexamples);

  /**
   * @brief
   *
   * @details
   */
  ~symex_learning_program_adaptert();

  /**
   * @brief
   *
   * @details
   */
  void operator()();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const symbol_tablet &get_adapted_symbol_table() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const goto_functionst &get_adapted_goto_functions() const;
};

#endif /* CEGIS_SYMEX_LEARNING_PROGRAM_ADAPTERT_H_ */
