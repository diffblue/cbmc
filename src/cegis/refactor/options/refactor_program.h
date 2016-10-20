/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_OPTIONS_REFACTOR_PROGRAM_H_
#define CEGIS_REFACTOR_OPTIONS_REFACTOR_PROGRAM_H_

#include <deque>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/goto_range.h>

/**
 * @brief
 *
 * @details
 */
class refactor_programt
{
public:
  symbol_tablet st;
  goto_functionst gf;

  /**
   * @brief
   *
   * @details All variable locations to be considered in counterexamples (including loop bodies).
   */
  goto_programt::targetst counterexample_locations;

  /**
   * @brief
   *
   * @details
   */
  class sketcht
  {
  public:
    goto_programt::targett init;
    goto_ranget input_range;
    goto_ranget spec_range;
    std::set<irep_idt> state_vars;
    std::set<typet> types;
    std::string processor_function;
  };

  /**
   * @brief
   *
   * @details
   */
  std::deque<sketcht> sketches;

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  explicit refactor_programt(const symbol_tablet &st, const goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  explicit refactor_programt(const refactor_programt &other);

  /**
   * @brief
   *
   * @details
   */
  explicit refactor_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  refactor_programt &operator=(const refactor_programt &other);
};

#endif /* CEGIS_REFACTOR_OPTIONS_REFACTOR_PROGRAM_H_ */
