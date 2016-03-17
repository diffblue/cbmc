/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_INDIVIDUAL_TO_SAFETY_SOLUTION_DESERIALISER_H_
#define CEGIS_INDIVIDUAL_TO_SAFETY_SOLUTION_DESERIALISER_H_

#include <cegis/safety/value/safety_goto_solution.h>

/**
 * @brief
 *
 * @details
 */
class individual_to_safety_solution_deserialisert
{
  const class safety_programt &prog;
  class instruction_set_info_factoryt &info_fac;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   * @param inf_fac
   */
  individual_to_safety_solution_deserialisert(const safety_programt &prog,
      instruction_set_info_factoryt &info_fac);

  /**
   * @brief
   *
   * @details
   */
  ~individual_to_safety_solution_deserialisert();

  /**
   * @brief
   *
   * @details
   *
   * @param result
   * @param sdu
   */
  void operator()(safety_goto_solutiont &result, const irept &sdu) const;
};

#endif /* CEGIS_INDIVIDUAL_TO_SAFETY_SOLUTION_DESERIALISER_H_ */
