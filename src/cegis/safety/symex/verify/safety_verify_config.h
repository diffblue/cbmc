/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_SYMEX_VERIFY_SAFETY_VERIFY_CONFIG_H
#define CPROVER_CEGIS_SAFETY_SYMEX_VERIFY_SAFETY_VERIFY_CONFIG_H

#include <deque>

#include <util/message.h>

#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/value/safety_goto_solution.h>

/**
 * @brief
 *
 * @details
 */
class safety_verify_configt
{
  const safety_programt &original_program;
  safety_programt program;
  goto_programt::targetst quantifiers;
public:
  /**
   * @brief Counterexample type for this CEGIS component.
   *
   * @details Counterexamples give a set of values used for the state variables.
   */
  typedef class safety_goto_cet counterexamplet;
  typedef std::deque<counterexamplet> counterexamplest;

  /**
   * @brief Candidate solution type for this CEGIS component.
   *
   * @details Solutions are provided as a set of GOTO function bodies
   * (goto_programt::instructionst) for function names.
   */
  typedef safety_goto_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param program
   */
  explicit safety_verify_configt(const safety_programt &program);

  /**
   * @brief
   *
   * @details
   */
  ~safety_verify_configt();

  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   */
  void process(const candidatet &candidate);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const symbol_tablet &get_symbol_table() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const goto_functionst &get_goto_functions() const;

  /**
   * @brief
   *
   * @details
   *
   * @param counterexamples
   * @param trace
   */
  void convert(counterexamplest &counterexamples,
      const class goto_tracet &trace);

  /**
   * @brief
   *
   * @details
   *
   * @param counterexample
   */
  void show_counterexample(
      messaget::mstreamt &os,
      const counterexamplet &counterexample) const;
};

#endif // CPROVER_CEGIS_SAFETY_SYMEX_VERIFY_SAFETY_VERIFY_CONFIG_H
