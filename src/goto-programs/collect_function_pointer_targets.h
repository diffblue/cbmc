/*******************************************************************\

Module: Collect Indirect Function Call Targets

Author: diffblue

Date: May 2019

\*******************************************************************/

/// \file
/// Collect Indirect Function Call Targets

#ifndef CPROVER_GOTO_PROGRAMS_COLLECT_FUNCTION_POINTER_TARGETS_H
#define CPROVER_GOTO_PROGRAMS_COLLECT_FUNCTION_POINTER_TARGETS_H

#include <util/irep.h>
#include <util/pointer_offset_size.h>

#include <map>
#include <set>

#include "compute_called_functions.h"
#include "remove_const_function_pointers.h"

class goto_modelt;

using possible_fp_targetst = remove_const_function_pointerst::functionst;

/// Function pointer removal state:
/// Keeping track of the results of preceding analyses: does-remove-const and
/// remove-const-function. Since we maintain state throughout analysing multiple
/// goto-programs, it is necessary to be able to merge state of two subsequent
/// analyses.
struct fp_statet
{
  bool remove_const_found_functions;
  bool code_removes_const;
  bool precise_const_removal;

  fp_statet()
    : remove_const_found_functions(true),
      code_removes_const(false),
      precise_const_removal(true)
  {
  }

  void merge(const fp_statet &new_state)
  {
    if(!new_state.remove_const_found_functions)
      remove_const_found_functions = false;
    if(new_state.code_removes_const)
      code_removes_const = true;
    if(!new_state.precise_const_removal)
      precise_const_removal = false;
  }
};

using fp_state_targetst = std::pair<fp_statet, possible_fp_targetst>;
using possible_fp_targets_mapt = std::map<irep_idt, fp_state_targetst>;

/// Go through the whole model and find all potential function the pointer at
///   all call sites
/// \param message_handler: a message handler for reporting
/// \param goto_model: model to search for potential functions
/// \return a map from ids to sets of function candidates
possible_fp_targets_mapt get_function_pointer_targets(
  message_handlert &message_handler,
  const goto_functionst &goto_functions,
  const symbol_tablet &symbol_table,
  bool only_remove_const_fps = false);

/// Houses the facilities for collecting function pointer targets via the
/// call-operator.
class collect_function_pointer_targetst
{
public:
  collect_function_pointer_targetst(
    message_handlert &message_handler,
    const symbol_tablet &symbol_table,
    bool only_resolve_const_fps);

  /// Interface for running the function pointer targets collection
  /// \param goto_functions: the function to search for potential targets
  /// \return the map id -> stateful_target <fp_state, candidates>
  possible_fp_targets_mapt operator()(const goto_functionst &goto_functions);

  /// Extract function name from \p called_functions
  /// \param called_function: the function call expression
  /// \return function identifier
  static irep_idt get_callee_id(const exprt &called_function);

  /// Compare the type of arguments of two functions
  /// \param call_type: first function type
  /// \param function_type: second function type
  /// \param name_space: the namespace to be used to analyse symbols
  /// \return true if argument types are compatible
  static bool arg_is_type_compatible(
    const typet &call_type,
    const typet &function_type,
    const namespacet &name_space);

  /// Compare the types of two functions
  /// \param return_value_used: flag indicating the return value usage
  /// \param call_type: first function type
  /// \param function_type: second function type
  /// \param name_space: the namespace to be used to analyse symbols
  /// \return true if types are compatible
  static bool is_type_compatible(
    bool return_value_used,
    const code_typet &call_type,
    const code_typet &function_type,
    const namespacet &name_space);

protected:
  messaget log;
  const namespacet ns;
  const symbol_tablet &symbol_table;
  bool only_resolve_const_fps;
  bool initialised;

  std::unordered_set<irep_idt> address_taken;

  using type_mapt = std::map<irep_idt, code_typet>;
  type_mapt type_map;

  /// Initialise the set of take addresses
  /// \param goto_functions: goto functions to search through
  void initialise_taken_addresses(const goto_functionst &goto_functions);

  /// Initialise the type map: function_id -> type
  /// \param goto_functions: goto functions to search through
  void initialise_type_map(const goto_functionst &goto_functions);

  /// Go through the whole model and find all potential function the pointer at
  ///   \p call site may point to
  /// \param goto_functions: goto functions to search for potential candidates
  /// \param call_site: the call site of the function pointer under analysis
  /// \return the set of the potential functions
  fp_state_targetst get_function_pointer_targets(
    const goto_functionst &goto_functions,
    goto_programt::const_targett &call_site);

  /// Go through a single function body and find all potential function the
  ///   pointer at \p call site may point to
  /// \param goto_program: function body to search for potential functions
  /// \param call_site: the call site of the function pointer under analysis
  /// \return the set of the potential functions
  fp_state_targetst get_function_pointer_targets(
    const goto_programt &goto_program,
    goto_programt::const_targett &call_site);

  /// Try to remove the const function pointers
  /// \param goto_program: the function body to run the const_removal_check on
  /// \param functions: the list of functions the const removal found
  /// \param pointer: the pointer to be resolved
  fp_state_targetst
  try_remove_const_fp(const goto_programt &goto_program, const exprt &pointer);

  /// Refine the \p type in case the forward declaration was incomplete
  /// \param type: the type to be refined
  /// \param code: the function call code to get the arguments from
  /// \return the refined call type
  static code_typet
  refine_call_type(const typet &type, const code_function_callt &code);
};

#endif // CPROVER_GOTO_PROGRAMS_COLLECT_FUNCTION_POINTER_TARGETS_H
