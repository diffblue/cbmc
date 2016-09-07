/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_SYMEX_VERIFY_H_
#define CEGIS_CONTROL_SYMEX_VERIFY_H_

#include <util/message.h>

#include <cegis/control/value/control_counterexample.h>
#include <cegis/control/value/control_solution.h>

/**
 * @brief
 *
 * @details
 */
class control_symex_verifyt
{
public:
  typedef control_counterexamplet counterexamplet;
  typedef control_counterexamplest counterexamplest;
  typedef control_solutiont candidatet;

  /**
   * @brief
   *
   * @details
   */
  explicit control_symex_verifyt();


  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   */
  void process(const candidatet &candidate) const;

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

#endif /* CEGIS_CONTROL_SYMEX_VERIFY_H_ */
