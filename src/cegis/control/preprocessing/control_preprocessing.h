/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_PREPROCESSING_CONTROL_PREPROCESSING_H
#define CPROVER_CEGIS_CONTROL_PREPROCESSING_CONTROL_PREPROCESSING_H

#include <cegis/control/options/control_program.h>

/**
 * @brief
 *
 * @details
 */
class control_preprocessingt
{
  control_programt control_program;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  explicit control_preprocessingt(
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
  void operator()(size_t max_length) const;

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
  const control_programt &get_program() const;
};

#endif // CPROVER_CEGIS_CONTROL_PREPROCESSING_CONTROL_PREPROCESSING_H
