/*******************************************************************\

Module: Goto Verifier for Covering Goals that stores Traces

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto verifier for covering goals that stores traces

#ifndef CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_WITH_TRACE_STORAGE_H
#define CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_WITH_TRACE_STORAGE_H

#include "goto_verifier.h"

#include "cover_goals_report_util.h"
#include "goto_trace_storage.h"
#include "incremental_goto_checker.h"
#include "properties.h"

template <class incremental_goto_checkerT>
class cover_goals_verifier_with_trace_storaget : public goto_verifiert
{
public:
  cover_goals_verifier_with_trace_storaget(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : goto_verifiert(options, ui_message_handler),
      goto_model(goto_model),
      incremental_goto_checker(options, ui_message_handler, goto_model),
      traces(incremental_goto_checker.get_namespace())
  {
    properties = initialize_properties(goto_model);
  }

  resultt operator()() override
  {
    while(incremental_goto_checker(properties).progress !=
          incremental_goto_checkert::resultt::progresst::DONE)
    {
      // we've got a trace; store it and link it to the covered goals
      (void)traces.insert_all(incremental_goto_checker.build_trace());

      ++iterations;
    }

    return determine_result(properties);
  }

  void report() override
  {
    output_goals(properties, iterations, ui_message_handler);
  }

  const goto_trace_storaget &get_traces() const
  {
    return traces;
  }

protected:
  abstract_goto_modelt &goto_model;
  incremental_goto_checkerT incremental_goto_checker;
  unsigned iterations = 1;
  goto_trace_storaget traces;
};

#endif // CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_WITH_TRACE_STORAGE_H
