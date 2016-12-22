/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_INSTRUCTION_ITERATOR_H
#define CPROVER_CEGIS_CEGIS_UTIL_INSTRUCTION_ITERATOR_H

#include <iterator>

#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details
 */
class instr_iteratort: public std::iterator<std::input_iterator_tag,
    goto_programt::instructiont>
{
  goto_functionst::function_mapt::iterator func_it;
  const goto_functionst::function_mapt::const_iterator func_end;
  goto_programt::targett prog_it;

  /**
   * @brief
   *
   * @details
   */
  instr_iteratort();
public:
  /**
   * @brief
   *
   * @details
   *
   * @param gf
   */
  explicit instr_iteratort(goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  instr_iteratort &operator++();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  instr_iteratort operator++(int);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  bool operator==(const instr_iteratort &other) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  bool operator!=(const instr_iteratort &other) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  reference operator*();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  pointer operator->();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  operator goto_programt::targett() const;

  /**
   * @brief
   *
   * @details
   */
  static const instr_iteratort end;
};

#endif // CPROVER_CEGIS_CEGIS_UTIL_INSTRUCTION_ITERATOR_H
