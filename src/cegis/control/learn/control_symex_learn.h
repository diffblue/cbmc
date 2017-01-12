/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_LEARN_CONTROL_SYMEX_LEARN_H
#define CPROVER_CEGIS_CONTROL_LEARN_CONTROL_SYMEX_LEARN_H

#include <util/message.h>

#include <cegis/control/value/control_counterexample.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/options/control_program.h>

/**
 * @brief
 *
 * @details
 */
template<class solution_configt>
class control_symex_learnt
{
  const control_programt &original_program;
  control_programt current_program;
public:
  typedef control_counterexamplet counterexamplet;
  typedef control_counterexamplest counterexamplest;
  typedef control_solutiont candidatet;
  /**
   * @brief
   *
   * @details
   *
   * @param original_program
   */
  explicit control_symex_learnt(const control_programt &original_program);

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

#include "control_symex_learn.inc"

#endif // CPROVER_CEGIS_CONTROL_LEARN_CONTROL_SYMEX_LEARN_H
