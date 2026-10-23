/*******************************************************************\

Module: Goto Verifier for Covering Goals that stores Traces

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto verifier for covering goals that stores traces

#ifndef CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_WITH_TRACE_STORAGE_H
#define CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_WITH_TRACE_STORAGE_H

#include "bmc_util.h"
#include "cover_goals_report_util.h"
#include "goto_trace_storage.h"
#include "goto_verifier.h"
#include "incremental_goto_checker.h"
#include "proof_explanation.h"
#include "properties.h"
#include "report_util.h"

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
      if(
        options.get_bool_option("show-test-suite") ||
        options.get_bool_option("trace"))
      {
        // we've got a trace; store it and link it to the covered goals
        message_building_error_trace(log);
        (void)traces.insert_all(incremental_goto_checker.build_full_trace());
      }

      ++iterations;
    }

    return determine_result(properties);
  }

  void report() override
  {
    output_goals(properties, iterations, ui_message_handler);
    if constexpr(has_get_proof_explanationt<incremental_goto_checkerT>::value)
    {
      if(options.get_bool_option("proof-explanation"))
      {
        bool has_unreachable =
          count_properties(properties, property_statust::PASS) > 0;
        if(has_unreachable)
        {
          // Overall explanation
          auto explanation = incremental_goto_checker.get_proof_explanation();
          output_proof_explanation(explanation, ui_message_handler);

          // Per-goal explanations (captured during incremental solving)
          auto per_prop =
            incremental_goto_checker.get_per_property_proof_explanations();
          // Filter to only unreachable goals (PASS in coverage = unreachable)
          std::map<irep_idt, std::vector<proof_explanation_stept>> unreachable;
          for(const auto &entry : per_prop)
          {
            auto it = properties.find(entry.first);
            if(
              it != properties.end() &&
              it->second.status == property_statust::PASS)
            {
              unreachable.insert(entry);
            }
          }
          if(!unreachable.empty())
            output_per_property_proof_explanations(
              unreachable, ui_message_handler);
        }
      }
    }
    if constexpr(has_get_proof_invariantst<incremental_goto_checkerT>::value)
    {
      if(options.get_bool_option("proof-explanation"))
      {
        bool has_unreachable =
          count_properties(properties, property_statust::PASS) > 0;
        if(has_unreachable)
        {
          auto invariants = incremental_goto_checker.get_proof_invariants();
          output_proof_invariants(invariants, ui_message_handler);
        }
      }
    }
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
