/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_SAFETY_PROGRAM_H_
#define CEGIS_SAFETY_PROGRAM_H_

#include <cegis/invariant/options/invariant_program.h>

/**
 * @brief
 *
 * @details
 */
class safety_programt: public invariant_programt
{
public:
  typedef std::vector<invariant_programt::invariant_loopt> safety_loopst;
  safety_loopst safety_loops;

  /**
   * @brief
   *
   * @details
   */
  safety_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  safety_programt(const safety_programt &other);

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  safety_programt(const symbol_tablet &st, const class goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   */
  virtual ~safety_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   *
   * @return
   */
  safety_programt &operator=(const safety_programt &other);

  /**
   * @see invariant_programt::get_loops
   */
  virtual const_invariant_loopst get_loops() const;

  /**
   * @see invariant_programt::get_loops
   */
  virtual invariant_loopst get_loops();

  /**
   * @see invariant_programt::add_loop
   */
  virtual invariant_loopt &add_loop();
};

#endif /* CEGIS_SAFETY_PROGRAM_H_ */
