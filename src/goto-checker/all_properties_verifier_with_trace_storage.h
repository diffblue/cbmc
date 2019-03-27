/*******************************************************************\

Module: Goto Verifier for Verifying all Properties that stores Traces

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto verifier for verifying all properties that stores traces

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_TRACE_STORAGE_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_TRACE_STORAGE_H

#include "goto_verifier.h"

#include "bmc_util.h"
#include "goto_trace_storage.h"
#include "incremental_goto_checker.h"
#include "properties.h"
#include "report_util.h"

template <class incremental_goto_checkerT>
class all_properties_verifier_with_trace_storaget : public goto_verifiert
{
public:
  all_properties_verifier_with_trace_storaget(
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
    while(true)
    {
      const auto result = incremental_goto_checker(properties);
      if(result.progress == incremental_goto_checkert::resultt::progresst::DONE)
        break;

      // we've got an error trace
      if(options.get_bool_option("trace"))
      {
        message_building_error_trace(log);
        for(const auto &property_id : result.updated_properties)
        {
          if(properties.at(property_id).status == property_statust::FAIL)
          {
            // get correctly truncated error trace for property and store it
            (void)traces.insert(
              incremental_goto_checker.build_trace(property_id));
          }
        }
      }

      ++iterations;
    }

    return determine_result(properties);
  }

  void report() override
  {
    if(options.get_bool_option("trace"))
    {
      const trace_optionst trace_options(options);
      output_properties_with_traces(
        properties, traces, trace_options, iterations, ui_message_handler);
    }
    else
    {
      output_properties(properties, iterations, ui_message_handler);
    }
    output_overall_result(determine_result(properties), ui_message_handler);
  }

  const goto_trace_storaget &get_traces() const
  {
    return traces;
  }

protected:
  abstract_goto_modelt &goto_model;
  incremental_goto_checkerT incremental_goto_checker;
  std::size_t iterations = 1;
  goto_trace_storaget traces;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_TRACE_STORAGE_H
