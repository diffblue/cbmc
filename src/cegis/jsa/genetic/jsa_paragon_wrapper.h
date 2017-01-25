/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_GENETIC_JSA_PARAGON_WRAPPER_H
#define CPROVER_CEGIS_JSA_GENETIC_JSA_PARAGON_WRAPPER_H

#include <cegis/jsa/value/jsa_counterexample.h>
#include <cegis/jsa/value/jsa_genetic_solution.h>

/**
 * @brief
 *
 * @details
 */
class jsa_paragon_wrappert
{
  class jsa_symex_learnt &wrapped;
public:
  typedef jsa_counterexamplet counterexamplet;
  typedef jsa_counterexamplest counterexamplest;
  typedef jsa_genetic_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param wrapped
   */
  explicit jsa_paragon_wrappert(jsa_symex_learnt &wrapped);

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
      size_t max_solution_size) const;

  /**
   * @brief
   *
   * @details
   *
   * @param max_solution_size
   */
  void process(size_t max_solution_size) const;

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
      const candidatet &candidate) const;
};

#endif // CPROVER_CEGIS_JSA_GENETIC_JSA_PARAGON_WRAPPER_H
