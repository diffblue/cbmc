/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_LEARN_REFACTOR_SYMEX_LEARN_H
#define CPROVER_CEGIS_REFACTOR_LEARN_REFACTOR_SYMEX_LEARN_H

#include <util/message.h>

#include <cegis/refactor/options/refactor_program.h>
#include <cegis/refactor/value/refactor_counterexample.h>
#include <cegis/refactor/value/refactor_solution.h>

class refactor_symex_learnt
{
  const refactor_programt &original_program;
  refactor_programt current_program;
public:
  typedef refactor_counterexamplet counterexamplet;
  typedef refactor_counterexamplest counterexamplest;
  typedef refactor_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param original_program
   */
  explicit refactor_symex_learnt(const refactor_programt &original_program);

  /**
   * @brief
   *
   * @details
   *
   * @param counterexamples
   * @param max_solution_size
   */
  void process(
      const counterexamplest &counterexamples,
      size_t max_solution_size);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class symbol_tablet &get_symbol_table() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class goto_functionst &get_goto_functions() const;

  /**
   * @brief
   *
   * @details
   *
   * @param word_width_in_bits
   */
  void set_word_width(size_t word_width_in_bits) const;

  /**
   * @brief
   *
   * @details
   *
   * @param current_candidate
   * @param trace
   * @param max_solution_size
   */
  void convert(
      candidatet &current_candidate,
      const class goto_tracet &trace,
      size_t max_solution_size) const;

  /**
   * @brief
   *
   * @details
   *
   * @param os
   * @param candidate
   */
  void show_candidate(
      messaget::mstreamt &os,
      const candidatet &candidate) const;
};

#endif // CPROVER_CEGIS_REFACTOR_LEARN_REFACTOR_SYMEX_LEARN_H
