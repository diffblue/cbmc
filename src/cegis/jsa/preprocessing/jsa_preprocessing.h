/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_PREPROCESSING_JSA_PREPROCESSING_H
#define CPROVER_CEGIS_JSA_PREPROCESSING_JSA_PREPROCESSING_H

#include <cegis/jsa/options/jsa_program.h>

/**
 * @brief
 *
 * @details
 */
class jsa_preprocessingt
{
  const class optionst &options;
  jsa_programt original_program;
  jsa_programt current_program;
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
  jsa_preprocessingt(
      const optionst &options,
      const symbol_tablet &st,
      const goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   */
  ~jsa_preprocessingt();

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
  const jsa_programt &get_jsa_program() const;
};

#endif // CPROVER_CEGIS_JSA_PREPROCESSING_JSA_PREPROCESSING_H
