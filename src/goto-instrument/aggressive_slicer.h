/*******************************************************************\

Module: Aggressive Slicer

Author: Elizabeth Polgreen, polgreen@amazon.com

\*******************************************************************/

/// \file
/// Aggressive slicer
/// Consider the control flow graph of the goto program and a criterion
/// description of aggressive slicer here

#ifndef CPROVER_GOTO_INSTRUMENT_AGGRESSIVE_SLICER_H
#define CPROVER_GOTO_INSTRUMENT_AGGRESSIVE_SLICER_H

#include <list>
#include <string>
#include <unordered_set>

#include <util/irep.h>

#include <analyses/call_graph.h>

#include <linking/static_lifetime_init.h>

class goto_modelt;
class message_handlert;

/// \brief The aggressive slicer removes the body of all the functions except
/// those on the shortest path, those within the call-depth of the
/// shortest path, those given by name as command line argument,
/// and those that contain a given irep_idt snippet
/// If no properties are set by the user, we preserve all functions on
/// the shortest paths to each property.
class aggressive_slicert
{
public:
  aggressive_slicert(goto_modelt &_goto_model, message_handlert &_msg)
    : call_depth(0),
      preserve_all_direct_paths(false),
      start_function(_goto_model.goto_functions.entry_point()),
      goto_model(_goto_model),
      message_handler(_msg)
  {
    call_grapht undirected_call_graph =
      call_grapht::create_from_root_function(goto_model, start_function, false);
    call_graph = undirected_call_graph.get_directed_graph();
  }

  ///  \brief Removes the body of all functions except those on the
  /// shortest path or functions
  /// that are reachable from functions on the shortest path within
  /// N calls, where N is given by the parameter "distance"
  void doit();

  /// \brief Adds a list of functions to the set of functions for the aggressive
  /// slicer to preserve
  /// \param function_list: a list of functions in form std::list<std::string>,
  ///   as returned by get_cmdline_option.
  void preserve_functions(const std::list<std::string> &function_list)
  {
    for(const auto &f : function_list)
      functions_to_keep.insert(f);
  };

  std::list<std::string> user_specified_properties;
  std::size_t call_depth;
  std::list<std::string> name_snippets;
  bool preserve_all_direct_paths;

private:
  const irep_idt start_function;
  goto_modelt &goto_model;
  message_handlert &message_handler;
  std::set<irep_idt> functions_to_keep;
  call_grapht::directed_grapht call_graph;

  /// \brief Finds all functions whose name contains a name snippet
  /// and adds them to the std::unordered_set of irep_idts of functions
  /// for the aggressive slicer to preserve
  void find_functions_that_contain_name_snippet();

  /// \brief notes functions to keep in the slice based on the program
  /// start function and the given destination function. Functions are noted
  /// according to the configuration parameters set in the aggressive
  /// slicer, i.e., shortest path between two functions, or all direct paths.
  /// Inserts functions to preserve into the functions_to_keep set
  /// \param destination_function: name of destination function for slice
  void note_functions_to_keep(const irep_idt &destination_function);

  /// \brief Finds all functions that contain a property,
  /// and adds them to the list of functions to keep. This
  /// function is only called if no properties are given by the user.
  /// This behaviour mirrors the behaviour of the other program
  /// slicers (reachability, global, full)
  void get_all_functions_containing_properties();
};

// clang-format off
#define OPT_AGGRESSIVE_SLICER \
    "(aggressive-slice)" \
    "(aggressive-slice-call-depth):" \
    "(aggressive-slice-preserve-function):" \
    "(aggressive-slice-preserve-functions-containing):" \
    "(aggressive-slice-preserve-all-direct-paths)"

// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_AGGRESSIVE_SLICER_H
