/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_PREPROCESSING_SAFETY_PREPROCESSING_H
#define CPROVER_CEGIS_SAFETY_PREPROCESSING_SAFETY_PREPROCESSING_H

#include <cegis/invariant/constant/constant_strategy.h>
#include <cegis/safety/options/safety_program.h>

/**
 * @brief
 *
 * @details
 */
class safety_preprocessingt
{
  class optionst &options;
  safety_programt original_program;
  safety_programt current_program;
  const constant_strategyt constant_strategy;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param st
   * @param gf
   * @param constant_strategy
   */
  safety_preprocessingt(optionst &options, const symbol_tablet &st,
      const goto_functionst &gf, const constant_strategyt &constant_strategy);

  /**
   * @brief
   *
   * @details
   */
  ~safety_preprocessingt();

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
  void operator()(size_t max_solution_length);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const safety_programt &get_safety_program() const;
};

#endif // CPROVER_CEGIS_SAFETY_PREPROCESSING_SAFETY_PREPROCESSING_H
