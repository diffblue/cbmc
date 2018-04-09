/*******************************************************************\

Module: Slice Function Calls and Direct Dependency Parameters

Author: Matthias Güdemann, matthias.guedemann@diffblue.com

\*******************************************************************/

#include "slice_function_calls.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/suffix.h>

/// Remove function call and parameter definitions the call depends on
/// \param goto_function: the GOTO function to change
/// \param slice_function: the name of the function to slice away
void slice_function_calls(
  goto_model_functiont &goto_function,
  const std::string &slice_function)
{
  if(slice_function.empty())
    return;

  slice_function_callst sfc(slice_function);
  sfc(goto_function);
}

/// Slice away selected function call and parameters that have no other
/// dependencies than the sliced function call.
///
/// Builds a dependency graph (DAG) with nodes specifying the function call,
/// local variables, function parameter of the containing GOTO function and
/// "OTHER" GOTO instructions. A GOTO instruction is considered to be dependent
/// on a local variable if in any of its expressions the symbol corresponding to
/// that variable appears. After the construction we iteratively remove nodes
/// with no incoming nodes, i.e., nodes on which no other node depends, starting
/// with the removal of the sliced function call.
///
/// For each such freed local variable which is also a parameter to the sliced
/// function, we remove its DECL, DEAD and ASSIGN instructions.
///
/// \param goto_function: the GOTO function to change
void slice_function_callst::operator()(goto_model_functiont &goto_function)
{
  std::set<irep_idt> variable_set =
    compute_variable_set(goto_function.get_goto_function());

#ifdef DEBUG
  for(const auto &entry : variable_set)
  {
    std::cout << "variable " << id2string(entry) << std::endl;
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
  std::set<unsigned> location_numbers_to_remove;

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
    root_node.node_index = root_index;
    slice_function_graph[root_index] = root_node;

    unsigned slice_function_location = root_node.location_number;

    slice_nodest slice_nodes = get_function_parameters(
      variable_set, entry.second, entry.first.second);

    for(auto &node : slice_nodes)
    {
      slice_nodet::node_indext index = slice_function_graph.add_node();
      node.node_index = index;
      slice_function_graph[index] = node;
      slice_function_graph.add_edge(root_index, index);

#ifdef DEBUG
      std::cout << "connect " << root_index << " and " << index << std::endl;
#endif
    }

    // see where the function parameters are also referenced
    for(const auto &instruction :
        goto_function.get_goto_function().body.instructions)
    {
      if(instruction.location_number == slice_function_location)
        continue;

      for(const auto &node : slice_nodes)
      {
        if(is_referenced(instruction, node.name))
        {
#ifdef DEBUG
          std::cout << "Found " << node.name << " in instruction "
                    << instruction.to_string() << std::endl;
#endif
          // create new "other" node
          slice_nodet slice_node;
          slice_node.slice_node_type = slice_node_typet::OTHER;
          slice_node.location_number = instruction.location_number;
          slice_nodet::node_indext node_index = slice_function_graph.add_node();
          slice_node.node_index = node_index;
          slice_function_graph[node_index] = slice_node;
          slice_function_graph.add_edge(node_index, node.node_index);
#ifdef DEBUG
          std::cout << "connect " << node_index << " and " << node.node_index
                    << std::endl;
#endif
        }
      }
    }

    size_t graph_size = slice_function_graph.size();

    // remove edges from dependency graph
    bool changed = true;
    while(changed)
    {
      changed = false;
      // find sliceable (non-OTHER) node without incoming dependencies
      for(size_t i = 0; i < graph_size; i++)
      {
        const slice_nodet &slice_node = slice_function_graph[i];
        if(slice_node.slice_node_type == slice_node_typet::OTHER)
          continue;

        const auto &in_edges = slice_function_graph.in(i);
        const auto &out_edges = slice_function_graph.out(i);
        if(in_edges.empty() && !out_edges.empty())
        {
#ifdef DEBUG
          std::cout << "found empty in_edges for active node " << i << std::endl;
#endif
          for(const auto &out_edge : out_edges)
          {
            slice_function_graph.remove_edge(i, out_edge.first);
#ifdef DEBUG
            std::cout << "remove (" << i << ", " << out_edge.first << ") ";
#endif
          }
          changed = true;
#ifdef DEBUG
          std::cout << std::endl;
#endif

          // add sliced function call to instructions to remove
          if(slice_node.slice_node_type == slice_node_typet::FUNCTION_CALL)
            location_numbers_to_remove.insert(slice_node.location_number);
        }
      }
    }
  }

  // remove decl/dead/assign for unused variables
  std::set<irep_idt> sliced_local_variables;
  size_t graph_size = slice_function_graph.size();
  for(size_t i = 0; i < graph_size; i++)
  {
    const slice_nodet &slice_node = slice_function_graph[i];
    if(slice_node.slice_node_type == slice_node_typet::LOCAL_VARIABLE)
    {
      if(slice_function_graph.in(i).empty())
        sliced_local_variables.insert(slice_node.name);
    }
  }

  // transform instructions to slice into SKIP
  for(auto &instruction : goto_function.get_goto_function().body.instructions)
  {
    if(
      location_numbers_to_remove.find(instruction.location_number) !=
      location_numbers_to_remove.end())
    {
      instruction.make_skip();
    }
    else if(
      instruction.type == goto_program_instruction_typet::DECL)
    {
      const code_declt &code_decl = to_code_decl(instruction.code);
      if(
        sliced_local_variables.find(code_decl.get_identifier()) !=
        sliced_local_variables.end())
      {
        instruction.make_skip();
      }
    }
    else if(instruction.type == goto_program_instruction_typet::DEAD)
    {
      const code_deadt &code_dead = to_code_dead(instruction.code);
      if(
        sliced_local_variables.find(code_dead.get_identifier()) !=
        sliced_local_variables.end())
      {
        instruction.make_skip();
      }
    }
    else if(instruction.type == goto_program_instruction_typet::ASSIGN)
    {
      const code_assignt &code_assign = to_code_assign(instruction.code);
      const exprt &lhs = code_assign.lhs();
      if(lhs.id() == ID_symbol)
      {
        const symbol_exprt &lhs_symbol_expr = to_symbol_expr(lhs);
        if(
          sliced_local_variables.find(lhs_symbol_expr.get_identifier()) !=
          sliced_local_variables.end())
        {
          instruction.make_skip();
        }
      }
    }
  }
}

/// Compute set of local variables, identified by corresponding DECL / DEAD GOTO
/// instructions.
/// \param goto_function: the GOTO function to analyze
/// \return: set of symbol identifiers of local variables in the function.
std::set<irep_idt>
slice_function_callst::compute_variable_set(const goto_functiont &goto_function)
{
  std::set<irep_idt> variable_set;
  std::map<irep_idt, unsigned> declarations;

  // search for declaration / dead pairs
  //
  // note: in Java, scopes cannot overlap!
  // note: in GOTO programs, scopes are encoded in variable names
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
      if(variable_set.find(var_name) == variable_set.end())
      {
        variable_set.insert(var_name);
        declarations.erase(var_name);
      }
      else
      {
        UNREACHABLE;
      }
    }
  }

  return variable_set;
}

/// Gets the correct slice_nodet for the given location function call.
/// \param variable_set: set of identifiers of local variables
/// \param param_set: set of names of function parameters
/// \param: location_number GOTO location number of function call
/// \return list of slice_nodes for dependency graph
slice_nodest slice_function_callst::get_function_parameters(
  const std::set<irep_idt> &variable_set,
  const std::set<irep_idt> &param_set,
  unsigned location_number)
{
  slice_nodest slice_nodes;
  for(const auto &var_name : param_set)
  {
    // is a function parameter
    if(variable_set.find(var_name) != variable_set.end())
    {
      slice_nodet slice_node;
      slice_node.name = var_name;
      slice_node.slice_node_type = slice_node_typet::LOCAL_VARIABLE;
      slice_nodes.push_back(slice_node);
    }
  }
  return slice_nodes;
}

/// Checks whether a variable is used in a GOTO instruction. This doesn't
/// concern declarations of that variable, assignment or dead statements.
/// \param instruction: the GOTO instruction to analyze
/// \param name: the name of the variable to search
/// \return true if found in the `exprt` of the instruction, else false
bool slice_function_callst::is_referenced(
  const goto_programt::instructiont &instruction,
  const irep_idt &name)
{
  std::set<irep_idt> seen;
  local_variable_visitort local_variable_visitor(seen);

  switch(instruction.type)
  {
    // inspect guard
  case goto_program_instruction_typet::GOTO:
  case goto_program_instruction_typet::ASSUME:
  case goto_program_instruction_typet::ASSERT:
  {
    instruction.guard.visit(local_variable_visitor);
    break;
  }

  // inspect rhs
  case goto_program_instruction_typet::ASSIGN:
  {
    const code_assignt &code_assign = to_code_assign(instruction.code);
    code_assign.rhs().visit(local_variable_visitor);
    break;
  }

  // inspect function parameter
  case goto_program_instruction_typet::FUNCTION_CALL:
  {
    const code_function_callt &fun_call =
      to_code_function_call(instruction.code);
    for(const auto &argument : fun_call.arguments())
      argument.visit(local_variable_visitor);
    break;
  }

    // cannot be referenced in the following instructions
  case goto_program_instruction_typet::RETURN:
  case goto_program_instruction_typet::DECL:
  case goto_program_instruction_typet::DEAD:
  case goto_program_instruction_typet::OTHER:
  case goto_program_instruction_typet::SKIP:
  case goto_program_instruction_typet::LOCATION:
  case goto_program_instruction_typet::ATOMIC_BEGIN:
  case goto_program_instruction_typet::ATOMIC_END:
  case goto_program_instruction_typet::END_FUNCTION:
  case goto_program_instruction_typet::START_THREAD:
  case goto_program_instruction_typet::THROW:
  case goto_program_instruction_typet::CATCH:
    break;

  default:
    UNREACHABLE;
  }

  return seen.find(name) != seen.end();
}

/// Visit expression and collect symbols, implements `operator()` of
/// `const_expr_visitort`.
/// \param expr: expression to visit
void slice_function_callst::local_variable_visitort::operator()(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    const symbol_exprt symbol_expr = to_symbol_expr(expr);
    const irep_idt &identifier = symbol_expr.get_identifier();

    seen.insert(identifier);
  }
}
