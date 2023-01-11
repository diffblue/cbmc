/*******************************************************************\

Module: Dump Loop Contracts as JSON

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Dump Loop Contracts as JSON

#include "dump_loop_contracts.h"

#include <util/json_stream.h>
#include <util/simplify_expr.h>

#include <ansi-c/expr2c.h>

void dump_loop_contracts(
  goto_modelt &goto_model,
  const std::map<loop_idt, exprt> &invariant_map,
  const std::map<loop_idt, std::set<exprt>> &assigns_map,
  const std::string &json_output_str,
  std::ostream &out)
{
  //  {
  //    "source"    : [SOURCE_NAME_ARRAY],
  //    "functions" : [{
  //                    FUN_NAME_1 : [LOOP_CONTRACTS_ARRAY],
  //                    FUN_NAME_2 : [LOOP_CONTRACTS_ARRAY],
  //                    ...
  //                  }],
  //    "output"    : OUTPUT
  //  }

  INVARIANT(!invariant_map.empty(), "No synthesized loop contracts to dump");

  namespacet ns(goto_model.symbol_table);

  // Set of names of source files.
  std::set<std::string> sources_set;

  // Map from function name to LOOP_CONTRACTS_ARRAY json array of the function.
  std::map<std::string, json_arrayt> function_map;

  json_arrayt json_sources;

  for(const auto &invariant_entry : invariant_map)
  {
    const auto head = get_loop_head(
      invariant_entry.first.loop_number,
      goto_model.goto_functions
        .function_map[invariant_entry.first.function_id]);

    const auto source_file = id2string(head->source_location().get_file());
    // Add source files.
    if(sources_set.insert(source_file).second)
      json_sources.push_back(json_stringt(source_file));

    // Get the LOOP_CONTRACTS_ARRAY for the function from the map.
    auto it_function =
      function_map.find(id2string(head->source_location().get_function()));
    if(it_function == function_map.end())
    {
      std::string function_name =
        id2string(head->source_location().get_function());

      // New LOOP_CONTRACTS_ARRAY
      json_arrayt loop_contracts_array;
      it_function =
        function_map.emplace(function_name, loop_contracts_array).first;
    }
    json_arrayt &loop_contracts_array = it_function->second;

    // Adding loop invariants
    // The loop number in Crangler is 1-indexed instead of 0-indexed.
    std::string inv_string =
      "loop " + std::to_string(invariant_entry.first.loop_number + 1) +
      " invariant " +
      expr2c(
        simplify_expr(invariant_entry.second, ns),
        ns,
        expr2c_configurationt::clean_configuration);
    loop_contracts_array.push_back(json_stringt(inv_string));

    // Adding loop assigns
    const auto it_assigns = assigns_map.find(invariant_entry.first);
    if(it_assigns != assigns_map.end())
    {
      std::string assign_string =
        "loop " + std::to_string(invariant_entry.first.loop_number + 1) +
        " assigns ";

      bool in_first_iter = true;
      for(const auto &a : it_assigns->second)
      {
        if(!in_first_iter)
        {
          assign_string += ",";
        }
        else
        {
          in_first_iter = false;
        }
        assign_string += expr2c(
          simplify_expr(a, ns), ns, expr2c_configurationt::clean_configuration);
      }
      loop_contracts_array.push_back(json_stringt(assign_string));
    }
  }

  json_stream_objectt json_stream(out);
  json_stream.push_back("sources", json_sources);

  // Initialize functions object.
  json_arrayt json_functions;
  json_objectt json_functions_object;
  for(const auto &loop_contracts : function_map)
  {
    json_functions_object[loop_contracts.first] = loop_contracts.second;
  }
  json_functions.push_back(json_functions_object);
  json_stream.push_back("functions", json_functions);

  // Destination of the Crangler output.
  json_stringt json_output(json_output_str);
  json_stream.push_back("output", json_output);
}
