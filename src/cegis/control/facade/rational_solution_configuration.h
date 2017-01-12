/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_FACADE_RATIONAL_SOLUTION_CONFIGURATION_H_
#define CEGIS_CONTROL_FACADE_RATIONAL_SOLUTION_CONFIGURATION_H_

#include <util/message.h>

/**
 * @brief
 *
 * @details
 */
class rational_solution_configurationt
{
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  static void nondeterminise_solution_configuration(class symbol_tablet &st, class goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   *
   * @param current_candidate
   * @param trace
   */
  static void convert(class control_solutiont &current_candidate, const class goto_tracet &trace);

  /**
   * @brief
   *
   * @details
   *
   * @param os
   * @param candidate
   */
  static void show_candidate(messaget::mstreamt &os, const control_solutiont &candidate);
};

#endif /* CEGIS_CONTROL_FACADE_RATIONAL_SOLUTION_CONFIGURATION_H_ */
