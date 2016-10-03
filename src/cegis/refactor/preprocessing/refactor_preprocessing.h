/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_PREPROCESSING_REFACTOR_PREPROCESSING_H_
#define CEGIS_REFACTOR_PREPROCESSING_REFACTOR_PREPROCESSING_H_

#include <cegis/refactor/options/refactor_program.h>

/**
 * @brief
 *
 * @details
 */
class refactor_preprocessingt
{
public:
  /**
   * @brief
   *
   * @details
   */
  explicit refactor_preprocessingt();

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
};

#endif /* CEGIS_REFACTOR_PREPROCESSING_REFACTOR_PREPROCESSING_H_ */
