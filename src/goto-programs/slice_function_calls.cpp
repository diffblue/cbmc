/*******************************************************************\

Module: Slice Function Calls and Direct Dependency Parameters

Author: Matthias Güdemann, matthias.guedemann@diffblue.com

\*******************************************************************/

#include "slice_function_calls.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/suffix.h>

void slice_function_calls(
  goto_model_functiont &goto_function,
  const std::string &slice_function)
{
  if(slice_function.empty())
    return;

  slice_function_callst sfc(slice_function);
  sfc(goto_function);
}

void slice_function_callst::operator()(goto_model_functiont &goto_function)
{
  variable_bounds_mapt variable_bounds_map =
    compute_variable_bounds(goto_function.get_goto_function());

#ifdef DEBUG
  for(const auto &entry : variable_bounds_map)
  {
    std::cout << "variable " << id2string(entry.first);
    for(const auto &listentry : entry.second)
    {
      std::cout << " in [" << listentry.lower_bound << ", "
                << listentry.upper_bound << "]" << std::endl;
    }
  }
#endif

#ifdef DEBUG
  std::cout << "slicing away function call to " << slice_function << std::endl;
#endif
  // map (function_call id, location number) -> set of parameters
  std::map<std::pair<irep_idt, unsigned>, std::set<irep_idt>>
    function_param_map;
  for(const goto_programt::instructiont &instruction :
        goto_function.get_goto_function().body.instructions)
  {
    if(instruction.type == goto_program_instruction_typet::FUNCTION_CALL)
    {
      const code_function_callt &fun_call =
        to_code_function_call(instruction.code);

      const symbol_exprt &fun = to_symbol_expr(fun_call.function());

      const irep_idt &function_id = fun.get_identifier();
      if(!has_suffix(id2string(function_id), slice_function))
        continue;

#ifdef DEBUG
      std::cout << "\nINFO: found function call to " << fun.get_identifier()
                << " in function " << id2string(instruction.function)
                << std::endl;
      const code_typet &fun_call_type = to_code_type(fun.type());
      for(const auto &parameter : fun_call_type.parameters())
      {
        std::cout << " param type " << parameter.type().id();
        if(parameter.get_this())
        {
          std::cout << " is this";
        }
        std::cout << std::endl;
      }
#endif

      std::set<irep_idt> function_params;
      for(const auto &arg : fun_call.arguments())
      {
        // record symbol parameters, in general local variables that are used
        // as parameters in the function call
        if(arg.id() == ID_symbol)
        {
          const irep_idt &param_name = to_symbol_expr(arg).get_identifier();
          function_params.insert(param_name);
#ifdef DEBUG
          std::cout << " found param " << param_name << std::endl;
#endif
        }
        else if(arg.id() == ID_constant)
        {
#ifdef DEBUG
          std::cout << "  constant " << to_constant_expr(arg).get_value()
                    << std::endl;
#endif
        }
        else
        {
#ifdef DEBUG
          std::cout << "  unknown " << id2string(arg.id()) << std::endl;
#endif
        }
      }
      function_param_map[{fun.get_identifier(), instruction.location_number}] =
        function_params;
    }
  }

  // construct graph
  slice_function_grapht slice_function_graph;
  for(const auto &entry : function_param_map)
  {
#ifdef DEBUG
    std::cout << "INFO: call (" << entry.first.first
              << ", location number: " << entry.first.second << " ) ";
    for(const auto &param : entry.second)
    {
      std::cout << id2string(param) << " ";
    }
    std::cout << std::endl;
#endif

    slice_nodet root_node;
    root_node.slice_node_type = slice_node_typet::FUNCTION_CALL;
    root_node.name = entry.first.first;
    root_node.location_number = entry.first.second;
    slice_nodet::node_indext root_index = slice_function_graph.add_node();
    slice_function_graph[root_index] = root_node;

    slice_nodest slice_nodes = get_function_parameters(
      variable_bounds_map, entry.second, entry.first.second);

    for(const auto &node : slice_nodes)
    {
      slice_nodet::node_indext index = slice_function_graph.add_node();
      slice_function_graph[index] = node;
      slice_function_graph.add_edge(root_index, index);
#ifdef DEBUG
      std::cout << "connect " << root_index << " and " << index << std::endl;
#endif
    }
  }
}

slice_function_callst::variable_bounds_mapt
slice_function_callst::compute_variable_bounds(
  const goto_functiont &goto_function)
{
  slice_function_callst::variable_bounds_mapt variable_bounds_map;

  std::map<irep_idt, unsigned> declarations;

  // search for declaration / dead pairs
  //
  // note: in Java, scopes cannot overlap!
  for(const auto &instruction : goto_function.body.instructions)
  {
    if(instruction.type == goto_program_instruction_typet::DECL)
    {
      const code_declt &decl = to_code_decl(instruction.code);
      const irep_idt &var_name = decl.get_identifier();
      DATA_INVARIANT(
        declarations.find(var_name) == declarations.end(),
        "declarations cannot overlap");
      declarations[var_name] = instruction.location_number;
    }
    else if(instruction.type == goto_program_instruction_typet::DEAD)
    {
      const code_deadt &dead = to_code_dead(instruction.code);
      const irep_idt &var_name = dead.get_identifier();
      DATA_INVARIANT(
        declarations.find(var_name) != declarations.end(),
        "closing scope of undeclared variable");
      if(variable_bounds_map.find(var_name) == variable_bounds_map.end())
      {
        slice_param_boundst slice_param_bound;
        slice_param_bound.lower_bound = declarations[var_name];
        slice_param_bound.upper_bound = instruction.location_number;
        variable_bounds_map[var_name] = {slice_param_bound};
      }
      else
      {
        slice_param_boundst slice_param_bound;
        slice_param_bound.lower_bound = declarations[var_name];
        slice_param_bound.upper_bound = instruction.location_number;
        variable_bounds_map[var_name].push_back(slice_param_bound);
        declarations.erase(var_name);
      }
    }
  }

  return variable_bounds_map;
}

/// gets the correct slice_nodet for the given location number of the function
/// call
slice_nodest slice_function_callst::get_function_parameters(
  variable_bounds_mapt &variable_bounds_map,
  const std::set<irep_idt> &param_set,
  unsigned location_number)
{
  slice_nodest slice_nodes;
  for(const auto &var_name : param_set)
  {
    // is a function parameter
    if(variable_bounds_map.find(var_name) == variable_bounds_map.end())
    {
      slice_nodet slice_node;
      slice_node.name = var_name;
      slice_node.slice_node_type = slice_node_typet::FUNCTION_PARAMETER;
      slice_nodes.push_back(slice_node);
    }
    else
    {
      bool found = false;
      for(const auto &bounds : variable_bounds_map[var_name])
      {
        if(
          location_number >= bounds.lower_bound &&
          location_number <= bounds.upper_bound)
        {
          slice_nodet slice_node;
          slice_node.name = var_name;
          slice_node.slice_param_bounds = bounds;
          slice_node.slice_node_type = slice_node_typet::LOCAL_VARIABLE;
          slice_nodes.push_back(slice_node);
          found = true;
          break;
        }
      }
      DATA_INVARIANT(found, "local variable must be in scope");
    }
  }
  return slice_nodes;
}
