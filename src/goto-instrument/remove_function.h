/*******************************************************************\

Module: Remove function definition

Author: Michael Tautschnig

Date: April 2017

\*******************************************************************/

/// \file
/// Remove function definition

#ifndef CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H
#define CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H

#include <list>
#include <string>
#include <unordered_set>

#include <util/irep.h>

#include <analyses/call_graph.h>
#include <analyses/reachable_call_graph.h>

class goto_modelt;
class message_handlert;

void remove_function(
  goto_modelt &,
  const irep_idt &identifier,
  message_handlert &);

void remove_functions(
  goto_modelt &,
  const std::list<std::string> &names,
  message_handlert &);

/// \brief The aggressive slicer removes the body of all the functions except
/// those on the shortest path, those within the call-depth of the
/// shortest path, those given by name as command line argument,
/// and those that contain a given irep_idt snippet
/// If no properties are set by the user, we preserve all functions on
/// the shortest paths to each property.
class aggressive_slicert
{
public:
  aggressive_slicert(
      goto_modelt & _goto_model,
      message_handlert &_msg) :
      preserve_all_direct_paths(false),
      call_depth(0),
      start_function(_goto_model.goto_functions.entry_point()),
      goto_model(_goto_model),
      message_handler(_msg),
      call_graph(_goto_model),
      reach_graph()
      {
      }

  ///  \brief Removes the body of all functions except those on the
  /// shortest path or functions
  /// that are reachable from functions on the shortest path within
  /// N calls, where N is given by the parameter "distance"
  void doit();

  /// \brief Adds a list of functions to the set of functions for the aggressive
  /// slicer to preserve
  /// \param  function_list    a list of functions in form
  /// std::list<std::string>, as returned by get_cmdline_option.
  void preserve_functions(const std::list<std::string>& function_list)
  {
    for(const auto &f : function_list)
      functions_to_keep.insert(f);
  };

  /// \brief When set to true we preserve all functions on direct paths between
  /// the start function
  /// and any given properties. We do not allow this option to be used without
  /// specifying a property, as that would effectively be doing a full-slice
  bool preserve_all_direct_paths;
  std::list<std::string> properties;
  std::size_t call_depth;
  std::list<std::string> name_snippets;

private:
  irep_idt start_function;
  goto_modelt & goto_model;
  message_handlert & message_handler;
  std::unordered_set<irep_idt, irep_id_hash> functions_to_keep;
  call_grapht call_graph;
  reachable_call_grapht reach_graph;

  /// \brief Finds all functions whose name contains a name snippet
  /// and adds them to the std::unordered_set of irep_idts of functions
  /// for the aggressive slicer to preserve
  void find_functions_that_contain_name_snippet();

  /// \brief Finds all properties in the goto_model and writes their
  /// names to a list. This function is only called if no properties
  /// are given by the user
  void get_property_list();
};

#endif // CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H
