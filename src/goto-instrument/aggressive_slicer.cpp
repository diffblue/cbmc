/*******************************************************************\

Module: Aggressive slicer

Author: Elizabeth Polgreen, elizabeth.polgreen@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Aggressive program slicer

#include "aggressive_slicer.h"
#include "remove_function.h"
#include <analyses/call_graph_helpers.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/show_properties.h>
#include <util/message.h>

void aggressive_slicert::note_functions_to_keep(
  const irep_idt &destination_function)
{
  if(preserve_all_direct_paths)
  {
    /// Note that we have previously disconnected all nodes unreachable
    /// from the start function,
    /// which means that any reaching functions are also reachable from
    /// the start function.
    for(const auto &func :
        get_reaching_functions(call_graph, destination_function))
      functions_to_keep.insert(func);
  }
  else
  {
    for(const auto &func : get_shortest_function_path(
          call_graph, start_function, destination_function))
      functions_to_keep.insert(func);
  }
}

void aggressive_slicert::get_all_functions_containing_properties()
{
  for(const auto &fct : goto_model.goto_functions.function_map)
  {
    if(!fct.second.is_inlined())
    {
      for(const auto &ins : fct.second.body.instructions)
        if(ins.is_assert())
        {
          if(functions_to_keep.insert(fct.first).second)
            note_functions_to_keep(fct.first);
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
      if(id2string(f_it->first).find(name_snippet) != std::string::npos)
        functions_to_keep.insert(f_it->first);
    }
  }
}

void aggressive_slicert::doit()
{
  messaget message(message_handler);

  functions_to_keep.insert(INITIALIZE_FUNCTION);
  functions_to_keep.insert(start_function);

  // if no properties are specified, preserve all functions containing
  // any property
  if(user_specified_properties.empty())
  {
    message.debug() << "No properties given, so aggressive slicer "
                    << "is running over all possible properties"
                    << messaget::eom;
    get_all_functions_containing_properties();
  }

  // if a name snippet is given, get list of all functions containing
  // name snippet to preserve
  if(!name_snippets.empty())
    find_functions_that_contain_name_snippet();

  for(const auto &p : user_specified_properties)
  {
    auto property_loc = find_property(p, goto_model.goto_functions);
    if(!property_loc.has_value())
      throw "unable to find property in call graph";
    note_functions_to_keep(property_loc.value().get_function());
  }

  // Add functions within distance of shortest path functions
  // to the list
  if(call_depth != 0)
  {
    for(const auto &func : get_functions_reachable_within_n_steps(
          call_graph, functions_to_keep, call_depth))
      functions_to_keep.insert(func);
  }

  message.debug() << "Preserving the following functions \n";
  for(const auto &func : functions_to_keep)
    message.debug() << func << messaget::eom;

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(functions_to_keep.find(f_it->first) == functions_to_keep.end())
      remove_function(goto_model, f_it->first, message_handler);
  }
}
