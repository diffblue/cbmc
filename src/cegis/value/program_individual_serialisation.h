/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_VALUE_PROGRAM_INDIVIDUAL_SERIALISATION_H
#define CPROVER_CEGIS_VALUE_PROGRAM_INDIVIDUAL_SERIALISATION_H

#include <util/std_expr.h>

#include <cegis/value/program_individual.h>

/**
 * @brief
 *
 * @details
 *
 * @param step
 *
 * @return
 */
bool is_program_individual_decl(const class goto_trace_stept &step);

/**
 * @brief
 *
 * @details
 *
 * @param expr
 *
 * @return
 */
program_individualt::instructiont to_program_individual_instruction(
    const struct_exprt &expr);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param trace
 *
 * @return
 */
program_individualt to_program_individual(const class invariant_programt &prog,
    const class goto_tracet &trace);

/**
 * @brief
 *
 * @details
 *
 * @param prog
 * @param trace
 *
 * @return
 */
program_individualt to_program_individual(const class danger_programt &prog,
    const goto_tracet &trace);

/**
 * @brief
 *
 * @details
 *
 * @param sdu
 * @param individual
 */
void serialise(irept &sdu, const program_individualt &individual);

/**
 * @brief
 *
 * @details
 *
 * @param sdu
 * @param individual
 */
void deserialise(program_individualt &individual, const irept &sdu);

/**
 * @brief Deserialises and converts an individual.
 *
 * @details Deserialises an individual and converts it to a goto solution.
 */
class individual_to_danger_solution_deserialisert
{
  const danger_programt &prog;
  class instruction_set_info_factoryt &info_fac;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   * @param info_fac
   */
  individual_to_danger_solution_deserialisert(const danger_programt &prog,
      instruction_set_info_factoryt &info_fac);

  /**
   * @brief
   *
   * @details
   */
  ~individual_to_danger_solution_deserialisert();

  /**
   * @brief
   *
   * @details
   *
   * @param result
   * @param sdu
   */
  void operator()(class danger_goto_solutiont &result, const irept &sdu) const;
};

#endif // CPROVER_CEGIS_VALUE_PROGRAM_INDIVIDUAL_SERIALISATION_H
