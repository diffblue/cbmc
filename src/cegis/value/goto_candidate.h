/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_VALUE_GOTO_CANDIDATE_H_
#define CEGIS_VALUE_GOTO_CANDIDATE_H_

#include <goto-programs/goto_program.h>

/**
 * @brief GOTO program-based counterexample type.
 *
 * @details Counterexamples give a set of assignments (variable names and
 * corresponding assignments) for which the previous solution violates the
 * safety property.
 */
struct goto_candidatet
{
  /**
   * @brief
   *
   * @details
   */
  typedef std::map<const irep_idt, goto_programt::instructionst> bodiest;

  /**
   * @brief
   *
   * @details
   */
  bodiest bodies;

  /**
   * @brief
   *
   * @details
   */
  typedef std::map<const irep_idt, exprt> constantst;

  /**
   * @brief
   *
   * @details
   */
  constantst constants;
};

#endif /* CEGIS_VALUE_GOTO_CANDIDATE_H_ */
