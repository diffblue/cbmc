/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_DANGER_PROGRAM_H_
#define CEGIS_DANGER_PROGRAM_H_

#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details
 */
class danger_programt
{
public:
  /**
   * @brief
   *
   * @details
   */
  struct program_ranget
  {
    goto_programt::targett begin;
    goto_programt::targett end;
  };

  /**
   * @brief
   *
   * @details
   */
  struct meta_vars_positionst
  {
    goto_programt::targett Dx;
    goto_programt::targett Gx;
    goto_programt::targetst Rx;
    goto_programt::targetst Sx;
    goto_programt::targett Dx_prime;
    goto_programt::targetst Rx_prime;
  };

  /**
   * @brief
   *
   * @details
   */
  struct loopt
  {
    exprt guard;
    program_ranget body;
    goto_programt::targetst skolem_choices;
    meta_vars_positionst meta_variables;
  };
  typedef std::vector<loopt> loopst;

  symbol_tablet st;
  goto_functionst gf;
  loopst loops;
  goto_programt::targetst x0_choices;
  /**
   * @brief The range in the program relevant for danger analysis.
   *
   * @details Spans from the original beginning of the analysed program up to the
   * danger assertion.
   */
  program_ranget danger_range;
  exprt assertion;
  goto_programt::targett Dx0;
  goto_programt::targett Ax;

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
  ~danger_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  void set_goto_program(const symbol_tablet &st, const goto_functionst &gf);

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
};

#endif /* CEGIS_DANGER_PROGRAM_H_ */
