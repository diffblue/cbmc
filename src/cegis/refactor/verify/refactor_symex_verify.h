/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_REFACTOR_VERIFY_REFACTOR_SYMEX_VERIFY_H_
#define CEGIS_REFACTOR_VERIFY_REFACTOR_SYMEX_VERIFY_H_

#include <util/message.h>

#include <cegis/refactor/value/refactor_counterexample.h>
#include <cegis/refactor/value/refactor_solution.h>

/**
 * @brief
 *
 * @details
 */
class refactor_symex_verifyt
{
public:
  typedef refactor_counterexamplet counterexamplet;
  typedef refactor_counterexamplest counterexamplest;
  typedef refactor_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   */
  explicit refactor_symex_verifyt();

  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   */
  void process(const candidatet &candidate);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class symbol_tablet &get_symbol_table() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class goto_functionst &get_goto_functions() const;

  /**
   * @brief
   *
   * @details
   *
   * @param counterexamples
   * @param trace
   */
  void convert(
      counterexamplest &counterexamples,
      const class goto_tracet &trace) const;

  /**
   * @brief
   *
   * @details
   *
   * @param os
   * @param counterexample
   */
  void show_counterexample(
      messaget::mstreamt &os,
      const counterexamplet &counterexample) const;
};

#endif /* CEGIS_REFACTOR_VERIFY_REFACTOR_SYMEX_VERIFY_H_ */
