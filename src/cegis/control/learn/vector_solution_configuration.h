/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_LEARN_VECTOR_SOLUTION_CONFIGURATION_H_
#define CEGIS_CONTROL_LEARN_VECTOR_SOLUTION_CONFIGURATION_H_

#include <util/message.h>

/**
 * @brief
 *
 * @details
 */
class vector_solution_configurationt
{
public:
  vector_solution_configurationt()=delete;
  ~vector_solution_configurationt()=delete;


  /**
   * @brief
   *
   * @details
   */
  typedef class control_vector_solutiont solutiont;

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  static void nondeterminise_solution_configuration(
      class symbol_tablet &st,
      class goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   *
   * @param current_candidate
   * @param trace
   * @param st
   */
  static void convert(
      solutiont &current_candidate,
      const class goto_tracet &trace,
      const symbol_tablet &st);

  /**
   * @brief
   *
   * @details
   *
   * @param os
   * @param candidate
   * @param st
   */
  static void show_candidate(
      messaget::mstreamt &os,
      const solutiont &candidate,
      const symbol_tablet &st);
};

#endif /* CEGIS_CONTROL_LEARN_VECTOR_SOLUTION_CONFIGURATION_H_ */
