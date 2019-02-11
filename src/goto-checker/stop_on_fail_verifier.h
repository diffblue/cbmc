/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H

#include "bmc_util.h"
#include "goto_verifier.h"

/// Stops when the first failing property is found.
/// Requires an incremental goto checker that is a
/// `goto_trace_providert` and `witness_providert`.
template <class incremental_goto_checkerT>
class stop_on_fail_verifiert : public goto_verifiert
{
public:
  stop_on_fail_verifiert(
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
      incremental_goto_checker.output_proof();
      break;

    case resultt::FAIL:
    {
      message_building_error_trace(log);
      goto_tracet goto_trace = incremental_goto_checker.build_shortest_trace();
      output_error_trace(
        goto_trace,
        incremental_goto_checker.get_namespace(),
        trace_optionst(options),
        ui_message_handler);
      report_failure(ui_message_handler);
      incremental_goto_checker.output_error_witness(goto_trace);
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

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H
