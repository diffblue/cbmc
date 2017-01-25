/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_LAZY_GENETIC_SETTINGS_H
#define CPROVER_CEGIS_GENETIC_LAZY_GENETIC_SETTINGS_H

#include <functional>

#include <cegis/genetic/genetic_settings.h>

/**
 * @brief
 *
 * @details
 */
template<class wrappedt>
class lazy_genetic_settingst: public genetic_settingst
{
  wrappedt wrapped;
  std::pair<bool, size_t> stored_max_prog_sz;
  std::pair<bool, size_t> stored_num_progs;
  std::pair<bool, size_t> stored_num_vars;
  std::pair<bool, size_t> stored_num_consts;
  std::pair<bool, size_t> stored_num_x0;
public:
  /**
   * @brief
   *
   * @details
   */
  explicit lazy_genetic_settingst(const wrappedt &wrapped);

  /**
   * @brief
   *
   * @details
   */
  virtual ~lazy_genetic_settingst();

  /**
   * @see genetic_settingst::min_prog_sz(size_t)
   */
  virtual size_t min_prog_sz(size_t prog_index);

  /**
   * @see genetic_settingst::max_prog_sz(size_t)
   */
  virtual size_t max_prog_sz(size_t prog_index);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::function<size_t(void)> max_prog_sz_provider();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::function<size_t(size_t)> max_prog_sz_per_index_provider();

  /**
   * @see genetic_settingst::max_prog_sz()
   */
  virtual size_t max_prog_sz();

  /**
   * @see genetic_settingst::num_progs()
   */
  virtual size_t num_progs();

  /**
   * @see genetic_settingst::num_vars()
   */
  virtual size_t num_vars();

  /**
   * @see genetic_settingst::num_consts()
   */
  virtual size_t num_consts();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::function<size_t(void)> num_consts_provder();

  /**
   * @see genetic_settingst::num_x0()
   */
  virtual size_t num_x0();
};

#include "lazy_genetic_settings.inc"

#endif // CPROVER_CEGIS_GENETIC_LAZY_GENETIC_SETTINGS_H
