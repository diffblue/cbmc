/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_OPTIONS_JSA_PROGRAM_H
#define CPROVER_CEGIS_JSA_OPTIONS_JSA_PROGRAM_H

#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details JSA program for single-loop stream refactorings.
 */
class jsa_programt
{
public:
  symbol_tablet st;
  goto_functionst gf;

  /**
   * @brief
   *
   * @details All variables which get non-determinised at the inductive step.
   */
  goto_programt::targetst inductive_step_renondets;

  /**
   * @brief
   *
   * @details All variable locations to be considered in counterexamles (including loop bodies).
   */
  goto_programt::targetst counterexample_locations;

  /**
   * @brief
   *
   * @details Insertion position for synthetic variables (auto-generated constants, temps)
   */
  goto_programt::targett synthetic_variables;

  /**
   * @brief
   *
   * @details Base case assertion meta variable.
   */
  goto_programt::targett base_case;

  /**
   * @brief
   *
   * @details Invariant assumption meta variable.
   */
  goto_programt::targett inductive_assumption;

  /**
   * @brief
   *
   * @details Inductive step assertion meta variable.
   */
  goto_programt::targett inductive_step;

  /**
   * @brief
   *
   * @details Property entailment meta variable.
   */
  goto_programt::targett property_entailment;

  /**
   * @brief
   *
   * @details Expression of removed loop guard.
   */
  exprt guard;

  /**
   * @brief
   *
   * @details Body range from first to second (exclusive).
   */
  std::pair<goto_programt::targett, goto_programt::targett> body;

  /**
   * @brief
   *
   * @details
   */
  jsa_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  jsa_programt(const jsa_programt &other);

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  jsa_programt(const symbol_tablet &st, const goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   */
  ~jsa_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  jsa_programt &operator=(const jsa_programt &other);
};

#endif // CPROVER_CEGIS_JSA_OPTIONS_JSA_PROGRAM_H
