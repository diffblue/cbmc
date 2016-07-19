/*******************************************************************\

Module: Fault Localization

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_CBMC_FAULT_LOCALIZATION_H
#define CPROVER_CBMC_FAULT_LOCALIZATION_H

#include <util/namespace.h>
#include <util/options.h>
#include <util/threeval.h>
#include <langapi/language_ui.h>

#include <goto-symex/symex_target_equation.h>

#include "bv_cbmc.h"

class fault_localizationt
{
public:
  fault_localizationt(const optionst &_options)
    : options(_options)
  {
  }

  virtual ~fault_localizationt()
  {
  }

  void operator()(
    bv_cbmct &bv_cbmc,
    const symex_target_equationt &equation,
    const namespacet &ns);

protected:
  const optionst &options;

  // the failed property
  symex_target_equationt::SSA_stepst::const_iterator failed;

  // the list of localization points up to the failed property
  struct lpointt {
    goto_programt::const_targett target;
    unsigned score;
  };
  typedef std::map<literalt, lpointt> lpointst;
  lpointst lpoints;

  // this collects the guards as lpoints
  void collect_guards(
    const symex_target_equationt &equation);

  // specify an lpoint combination to check
  typedef std::vector<tvt> lpoints_valuet;
  bool check(
    prop_convt &prop_conv,
    const lpoints_valuet& value);
  void update_scores(
    const prop_convt &prop_conv,
    const lpoints_valuet& value);

  // localization method: flip each point
  void localize_linear(
    prop_convt &prop_conv);

  // localization method: TBD
  //void localize_TBD(
  //  prop_convt &prop_conv);

  symex_target_equationt::SSA_stepst::const_iterator get_failed_property(
    const prop_convt &prop_conv,
    const symex_target_equationt &equation);

  void report(bv_cbmct &bv_cbmc);
};

#endif
