/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_OPTIONS_INVARIANT_PROGRAM_H
#define CPROVER_CEGIS_INVARIANT_OPTIONS_INVARIANT_PROGRAM_H

#include <goto-programs/goto_functions.h>

/**
 * @brief
 *
 * @details
 */
class invariant_programt
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
    goto_programt::targett Ix;
    goto_programt::targett Gx;
    goto_programt::targett Ix_prime;
  };

  /**
   * @brief
   *
   * @details
   */
  struct invariant_loopt
  {
    exprt guard;
    program_ranget body;
    goto_programt::targetst skolem_choices;
    meta_vars_positionst meta_variables;
  };
  typedef std::vector<const invariant_loopt *> const_invariant_loopst;
  typedef std::vector<invariant_loopt *> invariant_loopst;

  symbol_tablet st;
  goto_functionst gf;
  /**
   * @brief The range in the program relevant for invariant analysis.
   *
   * @details Spans from the original beginning of the analysed program up to the
   * assertion.
   */
  program_ranget invariant_range;
  exprt assertion;
  goto_programt::targett Ix0;
  goto_programt::targett Ax;

  goto_programt::targetst x0_choices;

  /**
   * @brief
   *
   * @details
   */
  invariant_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   */
  invariant_programt(const symbol_tablet &st, const goto_functionst &gf);

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  invariant_programt(const invariant_programt &other);

  /**
   * @brief
   *
   * @details
   */
  virtual ~invariant_programt();

  /**
   * @brief
   *
   * @details
   *
   * @param other
   *
   * @return
   */
  invariant_programt &operator=(const invariant_programt &other);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual const_invariant_loopst get_loops() const = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual invariant_loopst get_loops() = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual invariant_loopt &add_loop() = 0;
};

#endif // CPROVER_CEGIS_INVARIANT_OPTIONS_INVARIANT_PROGRAM_H
