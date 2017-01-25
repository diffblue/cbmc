/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_REFACTOR_OPTIONS_REFACTOR_PROGRAM_H
#define CPROVER_CEGIS_REFACTOR_OPTIONS_REFACTOR_PROGRAM_H

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
   * @details
   */
  typedef std::map<const irep_idt, goto_programt::targetst> counterexample_locationst;

  /**
   * @brief
   *
   * @details All variable locations to be considered in counterexamples (including loop bodies).
   */
  counterexample_locationst counterexample_locations;

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
    typedef std::set<typet> typest;
    typest types;
  };

  /**
   * @brief
   *
   * @details
   */
  typedef std::deque<sketcht> sketchest;

  /**
   * @brief
   *
   * @details
   */
  sketchest sketches;

  /**
   * @brief
   *
   * @details
   */
  std::set<irep_idt> programs;

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

#endif // CPROVER_CEGIS_REFACTOR_OPTIONS_REFACTOR_PROGRAM_H
