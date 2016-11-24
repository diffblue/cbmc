/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_SETTINGS_H_
#define CEGIS_GENETIC_SETTINGS_H_

#include <cstddef>

/**
 * @brief
 *
 * @details
 */
class genetic_settingst
{
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog_index
   *
   * @return
   */
  virtual size_t min_prog_sz(size_t prog_index) = 0;

  /**
   * @brief
   *
   * @details
   *
   * @param prog_index
   *
   * @return
   */
  virtual size_t max_prog_sz(size_t prog_index) = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual size_t max_prog_sz() = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual size_t num_progs() = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual size_t num_vars() = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual size_t num_consts() = 0;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  virtual size_t num_x0() = 0;

  /**
   * @brief
   *
   * @details
   */
  virtual ~genetic_settingst();
};

#endif /* CEGIS_GENETIC_SETTINGS_H_ */
