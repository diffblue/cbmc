/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_GOTO_CE_H_
#define CEGIS_SAFETY_GOTO_CE_H_

#include <util/expr.h>

/**
 * @brief
 *
 * @details
 */
struct safety_goto_cet
{
  typedef std::map<const irep_idt, exprt> assignmentst;
  typedef std::vector<assignmentst> assignments_per_loopt;

  /**
   * @brief x0 assignment.
   *
   * @details Initial assignment. Indicates that I(x) => S(x) doesn't hold.
   */
  assignmentst x0;

  /**
   * @brief x assignments.
   *
   * @details Assignments for each loop constraint. Indicates that
   * \forall_x (Si(x) && G(x) => Si'(x)) && (Si(x) && -G(x) => A(x))
   * doesn't hold.
   */
  assignments_per_loopt x;

  /**
   * @brief
   *
   * @details
   *
   * @param other
   * @return
   */
  bool operator==(const safety_goto_cet &other) const;
};

#endif /* CEGIS_SAFETY_GOTO_CE_H_ */
