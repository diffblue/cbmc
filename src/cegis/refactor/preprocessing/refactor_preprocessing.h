/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_PREPROCESSING_REFACTOR_PREPROCESSING_H
#define CPROVER_CEGIS_REFACTOR_PREPROCESSING_REFACTOR_PREPROCESSING_H

#include <cegis/refactor/options/refactor_program.h>

/**
 * @brief
 *
 * @details
 */
class refactor_preprocessingt
{
  const class optionst &options;
  refactor_programt original_program;
  refactor_programt current_program;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param st
   * @param gf
   */
  explicit refactor_preprocessingt(
      const optionst &options,
      const symbol_tablet &st,
      const goto_functionst &gf);

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
   * @param max_length
   */
  void operator()(size_t max_length);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  size_t get_min_solution_size() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const refactor_programt &get_program() const;
};

#endif // CPROVER_CEGIS_REFACTOR_PREPROCESSING_REFACTOR_PREPROCESSING_H
