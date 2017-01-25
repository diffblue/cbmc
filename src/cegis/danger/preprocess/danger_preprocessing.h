/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_PREPROCESS_DANGER_PREPROCESSING_H
#define CPROVER_CEGIS_DANGER_PREPROCESS_DANGER_PREPROCESSING_H

#include <cegis/invariant/constant/constant_strategy.h>
#include <cegis/danger/options/danger_program.h>

/**
 * @brief
 *
 * @details
 */
class danger_preprocessingt
{
  class optionst &options;
  danger_programt original_program;
  danger_programt current_program;
  const constant_strategyt constant_strategy;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   * @param constant_strategy
   */
  danger_preprocessingt(optionst &options, const symbol_tablet &st,
      const goto_functionst &gf, const constant_strategyt &constant_strategy);

  /**
   * @brief
   *
   * @details
   */
  ~danger_preprocessingt();

  /**
   * @brief Provides the minimum solution size.
   *
   * @details Properties like the number of skolem choices dictate the minimum
   * solution size.
   */
  size_t get_min_solution_size() const;

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
   * @param max_solution_length
   */
  void operator()(const size_t max_solution_length);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const danger_programt &get_danger_program() const;
};

#endif // CPROVER_CEGIS_DANGER_PREPROCESS_DANGER_PREPROCESSING_H
