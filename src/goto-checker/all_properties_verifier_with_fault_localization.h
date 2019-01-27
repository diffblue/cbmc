/*******************************************************************\

Module: Goto Verifier for Verifying all Properties and Localizing Faults

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto verifier for verifying all properties that stores traces
/// and localizes faults

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_FAULT_LOCALIZATION_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_FAULT_LOCALIZATION_H

#include "goto_verifier.h"

#include "fault_localization_provider.h"
#include "goto_trace_storage.h"
#include "incremental_goto_checker.h"
#include "properties.h"
#include "report_util.h"

/// Requires an incremental goto checker that is a
/// `goto_trace_providert` and `fault_localization_providert`.
template <class incremental_goto_checkerT>
class all_properties_verifier_with_fault_localizationt : public goto_verifiert
{
public:
  all_properties_verifier_with_fault_localizationt(
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
      message_building_error_trace(log);
      for(const auto &property_id : result.updated_properties)
      {
        if(properties.at(property_id).status == property_statust::FAIL)
        {
          // get correctly truncated error trace for property and store it
          (void)traces.insert(
            incremental_goto_checker.build_trace(property_id));

          fault_locations.insert(
            {property_id,
             incremental_goto_checker.localize_fault(property_id)});
        }
      }

      ++iterations;
    }

    return determine_result(properties);
  }

  void report() override
  {
    if(
      options.get_bool_option("trace") ||
      // currently --trace only affects plain text output
      ui_message_handler.get_ui() != ui_message_handlert::uit::PLAIN)
    {
      const trace_optionst trace_options(options);
      output_properties_with_traces_and_fault_localization(
        properties,
        traces,
        trace_options,
        fault_locations,
        iterations,
        ui_message_handler);
    }
    else
    {
      output_properties_with_fault_localization(
        properties, fault_locations, iterations, ui_message_handler);
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
  std::unordered_map<irep_idt, fault_location_infot> fault_locations;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_FAULT_LOCALIZATION_H
