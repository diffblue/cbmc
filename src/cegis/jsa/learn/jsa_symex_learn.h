/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_SYMEX_LEARN_H_
#define CEGIS_JSA_SYMEX_LEARN_H_

#include <deque>
#include <util/message.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_counterexample.h>
#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/pred_ops.h>

/**
 * @brief
 *
 * @details
 */
class jsa_symex_learnt
{
  const jsa_programt &original_program;
  jsa_programt program;
  pred_op_idst op_ids;
  pred_op_idst const_op_ids;
public:
  typedef jsa_counterexamplet counterexamplet;
  typedef jsa_counterexamplest counterexamplest;
  typedef jsa_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param program
   */
  jsa_symex_learnt(const jsa_programt &program);

  /**
   * @brief
   *
   * @details
   */
  ~jsa_symex_learnt();

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
   * @param word_width_in_bits
   */
  void set_word_width(size_t word_width_in_bits);

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
      size_t max_solution_size);

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
   * @param os
   * @param candidate
   */
  void show_candidate(
      messaget::mstreamt &os,
      const candidatet &candidate);
};

#endif /* CEGIS_JSA_SYMEX_LEARN_H_ */
