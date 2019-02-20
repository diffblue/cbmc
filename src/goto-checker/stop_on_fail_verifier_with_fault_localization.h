/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property
        and localizing the fault

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property
/// and localizing the fault

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_WITH_FAULT_LOCALIZATION_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_WITH_FAULT_LOCALIZATION_H

#include "bmc_util.h"
#include "fault_localization_provider.h"
#include "goto_verifier.h"

/// Stops when the first failing property is found and localizes the fault
/// Requires an incremental goto checker that is a
/// `goto_trace_providert` and `fault_localization_providert`.
template <class incremental_goto_checkerT>
class stop_on_fail_verifier_with_fault_localizationt : public goto_verifiert
{
public:
  stop_on_fail_verifier_with_fault_localizationt(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : goto_verifiert(options, ui_message_handler),
      goto_model(goto_model),
      incremental_goto_checker(options, ui_message_handler, goto_model)
  {
    properties = std::move(initialize_properties(goto_model));
  }

  resultt operator()() override
  {
    (void)incremental_goto_checker(properties);
    return determine_result(properties);
  }

  void report() override
  {
    switch(determine_result(properties))
    {
    case resultt::PASS:
      report_success(ui_message_handler);
      break;

    case resultt::FAIL:
    {
      const goto_tracet goto_trace =
        incremental_goto_checker.build_shortest_trace();
      const fault_location_infot fault_location =
        incremental_goto_checker.localize_fault(
          goto_trace.get_last_step().property_id);

      output_error_trace_with_fault_localization(
        goto_trace,
        incremental_goto_checker.get_namespace(),
        trace_optionst(options),
        fault_location,
        ui_message_handler);

      report_failure(ui_message_handler);
      break;
    }

    case resultt::UNKNOWN:
      report_inconclusive(ui_message_handler);
      break;

    case resultt::ERROR:
      report_error(ui_message_handler);
      break;
    }
  }

protected:
  abstract_goto_modelt &goto_model;
  incremental_goto_checkerT incremental_goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_WITH_FAULT_LOCALIZATION_H
