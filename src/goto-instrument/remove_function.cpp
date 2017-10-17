/*******************************************************************\

Module: Remove function definition

Author: Michael Tautschnig

Date: April 2017

\*******************************************************************/

/// \file
/// Remove function definition

#include "remove_function.h"
#include "function_modifies.h"

#include <util/message.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/show_properties.h>

#include <string>


void aggressive_slicert::get_property_list()
{
  for(const auto &fct : goto_model.goto_functions.function_map)
  {
    if(!fct.second.is_inlined())
    {
      for(const auto &ins : fct.second.body.instructions)
        if(ins.is_assert())
        {
          for(const auto &func : call_graph.shortest_function_path(
              start_function, ins.function))
          {
            functions_to_keep.insert(func);
          }
        }
    }
  }
}


void aggressive_slicert::find_functions_that_contain_name_snippet()
{
  for(const auto &name_snippet : name_snippets)
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      if(id2string(f_it->first).find(name_snippet)!=std::string::npos)
        functions_to_keep.insert(f_it->first);
    }
  }
}


void aggressive_slicert::doit()
{
  messaget message(message_handler);

  functions_to_keep.insert(CPROVER_PREFIX "initialize");
  functions_to_keep.insert(start_function);

  // if no properties are specified, get list of all properties
  if(properties.empty())
    get_property_list();

  // if a name snippet is given, get list of all functions containing
  // name snippet
  if(!name_snippets.empty())
    find_functions_that_contain_name_snippet();

  for(const auto &p : properties)
  {
    source_locationt property_loc = find_property(p, goto_model.goto_functions);
    irep_idt dest = property_loc.get_function();
    for(const auto &func : call_graph.shortest_function_path(
        start_function, dest))
      functions_to_keep.insert(func);
  }

  // Add functions within distance of shortest path functions
  // to the list
  if(call_depth != 0)
    call_graph.reachable_within_n_steps(call_depth, functions_to_keep);

  for(const auto &func : functions_to_keep)
    message.status() << "Keeping: " << func << messaget::eom;

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(functions_to_keep.find(f_it->first)==functions_to_keep.end())
      remove_function(goto_model, f_it->first, message_handler);
  }
}

/// Remove the body of function "identifier" such that an analysis will treat it
/// as a side-effect free function with non-deterministic return value.
/// \par parameters: symbol_table  Input symbol table to be modified
/// goto_model  Input program to be modified
/// identifier  Function to be removed
/// message_handler  Error/status output
void remove_function(
  goto_modelt &goto_model,
  const irep_idt &identifier,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  goto_functionst::function_mapt::iterator entry=
    goto_model.goto_functions.function_map.find(identifier);

  if(entry==goto_model.goto_functions.function_map.end())
  {
    message.error() << "No function " << identifier
                    << " in goto program" << messaget::eom;
    return;
  }
  else if(entry->second.is_inlined())
  {
    message.warning() << "Function " << identifier << " is inlined, "
                      << "instantiations will not be removed"
                      << messaget::eom;
  }

  if(entry->second.body_available())
  {
    message.status() << "Removing body of " << identifier
                     << messaget::eom;
    entry->second.clear();
    goto_model.symbol_table.get_writeable_ref(identifier).value.make_nil();
  }
}

/// Remove the body of all functions listed in "names" such that an analysis
/// will treat it as a side-effect free function with non-deterministic return
/// value.
/// \par parameters: symbol_table  Input symbol table to be modified
/// goto_model  Input program to be modified
/// names  List of functions to be removed
/// message_handler  Error/status output
void remove_functions(
  goto_modelt &goto_model,
  const std::list<std::string> &names,
  message_handlert &message_handler)
{
  for(const auto &f : names)
    remove_function(goto_model, f, message_handler);
}
