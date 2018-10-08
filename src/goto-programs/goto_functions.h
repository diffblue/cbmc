/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H

#include "goto_function.h"

#include <util/cprover_prefix.h>

/// A collection of goto functions
class goto_functionst
{
public:
  using goto_functiont=::goto_functiont;
  typedef std::map<irep_idt, goto_functiont> function_mapt;
  function_mapt function_map;

private:
  /// A location number such that numbers in the interval
  /// [unused_location_number, MAX_UINT] are all unused. There might still be
  /// unused numbers below this.
  /// If numbering a new function or renumbering a function, starting from this
  /// number is safe.
  unsigned unused_location_number;

public:
  goto_functionst():
    unused_location_number(0)
  {
  }

  // Copying is unavailable as base class copy is deleted
  // MSVC is unable to automatically determine this
  goto_functionst(const goto_functionst &)=delete;
  goto_functionst &operator=(const goto_functionst &)=delete;

  // Move operations need to be explicitly enabled as they are deleted with the
  // copy operations
  // default for move operations isn't available on Windows yet, so define
  //  explicitly (see https://msdn.microsoft.com/en-us/library/hh567368.aspx
  //  under "Defaulted and Deleted Functions")

  goto_functionst(goto_functionst &&other):
    function_map(std::move(other.function_map)),
    unused_location_number(other.unused_location_number)
  {
  }

  goto_functionst &operator=(goto_functionst &&other)
  {
    function_map=std::move(other.function_map);
    unused_location_number=other.unused_location_number;
    return *this;
  }

  /// Remove function from the function map
  void unload(const irep_idt &name) { function_map.erase(name); }

  void clear()
  {
    function_map.clear();
  }

  void compute_location_numbers();
  void compute_location_numbers(goto_programt &);
  void compute_loop_numbers();
  void compute_target_numbers();
  void compute_incoming_edges();

  /// update the function member in each instruction by setting it to
  /// the goto function's identifier
  void update_instructions_function()
  {
    for(auto &func : function_map)
    {
      func.second.update_instructions_function(func.first);
    }
  }

  void update()
  {
    compute_incoming_edges();
    compute_target_numbers();
    compute_location_numbers();
    compute_loop_numbers();
    update_instructions_function();
  }

  /// Get the identifier of the entry point to a goto model
  static inline irep_idt entry_point()
  {
    // do not confuse with C's "int main()"
    return CPROVER_PREFIX "_start";
  }

  void swap(goto_functionst &other)
  {
    function_map.swap(other.function_map);
  }

  void copy_from(const goto_functionst &other)
  {
    for(const auto &fun : other.function_map)
      function_map[fun.first].copy_from(fun.second);
  }

  std::vector<function_mapt::const_iterator> sorted() const;
  std::vector<function_mapt::iterator> sorted();

  /// Check that the goto functions are well-formed
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  void validate(const namespacet &ns, const validation_modet vm) const
  {
    for(const auto &entry : function_map)
    {
      const goto_functiont &goto_function = entry.second;
      goto_function.validate(ns, vm);
    }
  }
};

#define Forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::iterator \
      it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

#define forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::const_iterator \
      it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H
