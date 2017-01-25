/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_VERIFY_DANGER_VERIFY_CONFIG_H
#define CPROVER_CEGIS_DANGER_SYMEX_VERIFY_DANGER_VERIFY_CONFIG_H

#include <deque>

#include <util/message.h>

#include <cegis/danger/options/danger_program.h>

/**
 * @brief
 *
 * @details
 */
class danger_verify_configt
{
  const danger_programt &original_program;
  danger_programt program;
  goto_programt::targetst quantifiers;
  bool limit_ce;
  size_t max_ce_width;
public:
  /**
   * @brief Counterexample type for this CEGIS component.
   *
   * @details Counterexamples give a set of values used for the state variables.
   */
  typedef std::map<const irep_idt, exprt> counterexamplet;
  typedef std::deque<counterexamplet> counterexamplest;

  /**
   * @brief Candidate solution type for this CEGIS component.
   *
   * @details Solutions are provided as a set of GOTO function bodies
   * (goto_programt::instructionst) for function names.
   */
  typedef class danger_goto_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param program
   */
  explicit danger_verify_configt(const danger_programt &program);

  /**
   * @brief
   *
   * @details
   */
  ~danger_verify_configt();

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
   * @return
   */
  goto_functionst &get_goto_functions();

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
   * @return
   */
  size_t get_number_of_loops() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  exprt::operandst get_loop_guards() const;

  /**
   * @brief
   *
   * @details
   *
   * @param size
   */
  void set_max_ce_width(size_t size);

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

#endif // CPROVER_CEGIS_DANGER_SYMEX_VERIFY_DANGER_VERIFY_CONFIG_H
