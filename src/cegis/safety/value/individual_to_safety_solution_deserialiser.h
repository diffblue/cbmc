/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_VALUE_INDIVIDUAL_TO_SAFETY_SOLUTION_DESERIALISER_H
#define CPROVER_CEGIS_SAFETY_VALUE_INDIVIDUAL_TO_SAFETY_SOLUTION_DESERIALISER_H

#include <functional>

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
   *
   * @param entity
   * @param sdu
   */
  void operator()(safety_goto_solutiont &entity, const irept &sdu) const;
};

#endif // CPROVER_CEGIS_SAFETY_VALUE_INDIVIDUAL_TO_SAFETY_SOLUTION_DESERIALISER_H
