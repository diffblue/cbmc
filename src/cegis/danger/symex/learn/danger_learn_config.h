/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_LEARN_DANGER_LEARN_CONFIG_H
#define CPROVER_CEGIS_DANGER_SYMEX_LEARN_DANGER_LEARN_CONFIG_H

#include <deque>

#include <util/message.h>

#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/value/danger_goto_solution.h>

/**
 * @brief
 *
 * @details
 */
class danger_learn_configt
{
public:
  /**
   * @brief
   *
   * @details
   */
  typedef std::map<const irep_idt, size_t> invariant_variable_idst;
private:
  const danger_programt &original_program;
  danger_programt program;
  invariant_variable_idst var_ids;
  size_t num_consts;
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
  typedef danger_goto_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param program
   */
  explicit danger_learn_configt(const danger_programt &program);

  /**
   * @brief
   *
   * @details
   */
  ~danger_learn_configt();

  /**
   * @brief
   *
   * @details
   *
   * @param counterexamples
   * @param max_solution_size
   */
  void process(const counterexamplest &counterexamples,
      size_t max_solution_size);

  /**
   * @brief Process the goto program using template data.
   *
   * @details Creates template counterexamples and processes the goto
   * program with them. This is useful for GA source code generation.
   *
   * @param max_solution_size
   */
  void process(size_t max_solution_size);

  /**
   * @brief
   *
   * @details
   *
   * @param word_width_in_bits
   */
  void set_word_width(size_t word_width_in_bits);

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
  const danger_programt &get_danger_program() const;

  /**
   * @brief
   *
   * @details
   *
   * @param current_candidate
   * @param trace
   * @param max_solution_size
   */
  void convert(candidatet &current_candidate, const class goto_tracet &trace,
      size_t max_solution_size);

  /**
   * @brief
   *
   * @details
   *
   * @param os
   * @param candidate
   */
  void show_candidate(messaget::mstreamt &os, const candidatet &candidate);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const invariant_variable_idst &get_vars() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  size_t get_num_vars() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  size_t get_num_consts() const;
};

#endif // CPROVER_CEGIS_DANGER_SYMEX_LEARN_DANGER_LEARN_CONFIG_H
