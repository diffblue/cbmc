/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_GENETIC_JSA_RANDOM_H
#define CPROVER_CEGIS_JSA_GENETIC_JSA_RANDOM_H

#include <functional>

#include <cegis/jsa/value/jsa_genetic_solution.h>

/**
 * @brief
 *
 * @details
 */
class jsa_randomt
{
  const class symbol_tablet &st;
  const std::function<size_t()> pred_ops_count;
  const std::function<size_t()> const_pred_ops_count;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param pred_ops_count
   * @param const_pred_ops_count
   */
  jsa_randomt(const symbol_tablet &st,
      std::function<size_t()> pred_ops_count,
      std::function<size_t()> const_pred_ops_count);

  /**
   * @brief
   *
   * @details
   *
   * @param individual
   */
  void havoc(jsa_genetic_solutiont &individual) const;

  /**
   * @brief
   *
   * @details
   *
   * @param predicates
   */
  void havoc(jsa_genetic_solutiont::predicatest &predicates) const;

  /**
   * @brief
   *
   * @details
   *
   * @param predicate
   */
  void havoc(jsa_genetic_solutiont::predicatet &predicate) const;

  /**
   * @brief
   *
   * @details
   *
   * @param instr
   */
  void havoc(jsa_genetic_solutiont::predicatet::value_type &instr) const;

  /**
   * @brief
   *
   * @details
   *
   * @param invariant
   */
  void havoc(jsa_genetic_solutiont::invariantt &invariant) const;

  /**
   * @brief
   *
   * @details
   *
   * @param instr
   */
  void havoc(jsa_genetic_solutiont::invariantt::value_type &instr) const;

  /**
   * @brief
   *
   * @details
   *
   * @param query
   */
  void havoc(jsa_genetic_solutiont::queryt &query) const;

  /**
   * @brief
   *
   * @details
   *
   * @param instr
   * @param index
   */
  void havoc(
      jsa_genetic_solutiont::queryt::value_type &instr,
      size_t index) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  void havoc_iterator(__CPROVER_jsa_opt &it) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  void havoc_list(__CPROVER_jsa_opt &list) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  void havoc_pred(__CPROVER_jsa_opt &pred) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  unsigned int rand() const;
};

#endif // CPROVER_CEGIS_JSA_GENETIC_JSA_RANDOM_H
