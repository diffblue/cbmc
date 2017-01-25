/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_SAFETY_OPTIONS_SAFETY_PROGRAM_GENETIC_SETTINGS_H
#define CPROVER_CEGIS_SAFETY_OPTIONS_SAFETY_PROGRAM_GENETIC_SETTINGS_H

#include <cegis/genetic/genetic_settings.h>

/**
 * @brief
 *
 * @details
 */
template<class preproct>
class safety_program_genetic_settingst: public genetic_settingst
{
  const class optionst &opt;
  const class safety_programt &prog;
  preproct &preproc;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param opt
   * @param prog
   * @param preproc
   */
  safety_program_genetic_settingst(const optionst &opt,
      const safety_programt &prog, preproct &preproc);

  /**
   * @brief
   *
   * @details
   */
  virtual ~safety_program_genetic_settingst();

  /**
   * @see genetic_settingst::min_prog_sz(size_t)
   */
  virtual size_t min_prog_sz(size_t prog_index);

  /**
   * @see genetic_settingst::max_prog_sz(size_t)
   */
  virtual size_t max_prog_sz(size_t prog_index);

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
   * @see genetic_settingst::num_x0()
   */
  virtual size_t num_x0();
};

#include "safety_program_genetic_settings.inc"

#endif // CPROVER_CEGIS_SAFETY_OPTIONS_SAFETY_PROGRAM_GENETIC_SETTINGS_H
