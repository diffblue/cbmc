/*******************************************************************\

Module: Fault Localization for Goto Symex

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Fault Localization for Goto Symex

#ifndef CPROVER_GOTO_CHECKER_GOTO_SYMEX_FAULT_LOCALIZER_H
#define CPROVER_GOTO_CHECKER_GOTO_SYMEX_FAULT_LOCALIZER_H

#include <util/options.h>
#include <util/threeval.h>
#include <util/ui_message.h>

#include <goto-symex/symex_target_equation.h>

#include "fault_localization_provider.h"

class goto_symex_fault_localizert
{
public:
  goto_symex_fault_localizert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    const symex_target_equationt &equation,
    prop_convt &solver);

  fault_location_infot operator()(const irep_idt &failed_property_id);

protected:
  const optionst &options;
  ui_message_handlert &ui_message_handler;
  const symex_target_equationt &equation;
  prop_convt &solver;

  /// A localization point is a goto instruction that is potentially at fault
  typedef std::map<literalt, fault_location_infot::score_mapt::iterator>
    localization_pointst;

  /// Collects the guards as \p localization_points up to \p failed_property_id
  /// and initializes fault_location_info, and returns the SSA step of
  /// the failed property
  const symex_target_equationt::SSA_stept &collect_guards(
    const irep_idt &failed_property_id,
    localization_pointst &localization_points,
    fault_location_infot &fault_location);

  // specify a localization point combination to check
  typedef std::vector<tvt> localization_points_valuet;
  bool check(
    const symex_target_equationt::SSA_stept &failed_step,
    const localization_pointst &,
    const localization_points_valuet &);

  void update_scores(const localization_pointst &);

  // localization method: flip each point
  void localize_linear(
    const symex_target_equationt::SSA_stept &failed_step,
    const localization_pointst &);
};

#endif // CPROVER_GOTO_CHECKER_GOTO_SYMEX_FAULT_LOCALIZER_H
