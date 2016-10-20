/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_PROGRAM_H_
#define CEGIS_CONTROL_PROGRAM_H_

#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details
 */
class control_programt
{
public:
  symbol_tablet st;
  goto_functionst gf;

  /**
   * @brief
   *
   * @details All variable locations to be considered in counterexamles (including loop bodies).
   */
  goto_programt::targetst counterexample_locations;

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  control_programt(const symbol_tablet &st, const goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  control_programt(const control_programt &other);

  /**
   * @brief
   *
   * @details
   */
  control_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  control_programt &operator=(const control_programt &other);
};

#endif /* CEGIS_CONTROL_PROGRAM_H_ */
