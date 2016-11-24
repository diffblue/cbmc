/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_PROGRAM_H_
#define CEGIS_DANGER_PROGRAM_H_

#include <cegis/invariant/options/invariant_program.h>

/**
 * @brief
 *
 * @details
 */
class danger_programt: public invariant_programt
{
public:
  /**
   * @brief
   *
   * @details
   */
  struct danger_meta_vars_positionst
  {
    goto_programt::targetst Rx;
    goto_programt::targetst Sx;
    goto_programt::targetst Rx_prime;
  };

  /**
   * @brief
   *
   * @details
   */
  struct loopt: public invariant_loopt
  {
    danger_meta_vars_positionst danger_meta_variables;
  };
  typedef std::vector<loopt> loopst;

  loopst loops;

  /**
   * @brief
   *
   * @details
   */
  danger_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  danger_programt(const danger_programt &other);

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  danger_programt(const symbol_tablet &st, const goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   */
  virtual ~danger_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   *
   * @return
   */
  danger_programt &operator=(const danger_programt &other);

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

#endif /* CEGIS_DANGER_PROGRAM_H_ */
