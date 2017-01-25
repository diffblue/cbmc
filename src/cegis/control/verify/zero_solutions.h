/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_VERIFY_ZERO_SOLUTIONS_H
#define CPROVER_CEGIS_CONTROL_VERIFY_ZERO_SOLUTIONS_H

/**
 * @brief
 *
 * @details
 *
 * @param st
 *
 * @return
 */
bool is_vector_solution_config(const class symbol_tablet &st);

/**
 * @brief
 *
 * @details
 */
class zero_rational_solutiont
{
  const symbol_tablet &st;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   */
  zero_rational_solutiont(const symbol_tablet &st);

  /**
   * @brief
   *
   * @details
   *
   * @param solution
   */
  void operator()(class control_solutiont &solution) const;
};

/**
 * @brief
 *
 * @details
 */
class zero_vector_solutiont
{
  const symbol_tablet &st;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   */
  zero_vector_solutiont(const symbol_tablet &st);

  /**
   * @brief
   *
   * @details
   *
   * @param solution
   */
  void operator()(class control_vector_solutiont &solution) const;
};

#endif // CPROVER_CEGIS_CONTROL_VERIFY_ZERO_SOLUTIONS_H
