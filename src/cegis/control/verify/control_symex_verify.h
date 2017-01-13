/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CONTROL_VERIFY_CONTROL_SYMEX_VERIFY_H
#define CPROVER_CEGIS_CONTROL_VERIFY_CONTROL_SYMEX_VERIFY_H

#include <util/message.h>

#include <cegis/control/value/control_counterexample.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/options/control_program.h>

/**
 * @brief
 *
 * @details
 */
template<class solutiont>
class control_symex_verifyt
{
  const control_programt &original_program;
  control_programt current_program;
public:
  typedef control_counterexamplet counterexamplet;
  typedef control_counterexamplest counterexamplest;
  typedef solutiont candidatet;

  /**
   * @brief
   *
   * @details
   *
   * @param original_program
   */
  explicit control_symex_verifyt(const control_programt &original_program);

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

#include "control_symex_verify.inc"

#endif // CPROVER_CEGIS_CONTROL_VERIFY_CONTROL_SYMEX_VERIFY_H
