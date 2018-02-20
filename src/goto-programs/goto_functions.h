/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H

#include "goto_program.h"

#include <ostream>
#include <cassert>

#include <util/std_types.h>
#include <util/symbol.h>
#include <util/cprover_prefix.h>

class goto_functiont
{
public:
  goto_programt body;
  code_typet type;

  typedef std::vector<irep_idt> parameter_identifierst;
  parameter_identifierst parameter_identifiers;

  bool body_available() const
  {
    return !body.instructions.empty();
  }

  bool is_inlined() const
  {
    return type.get_bool(ID_C_inlined);
  }

  bool is_hidden() const
  {
    return type.get_bool(ID_C_hide);
  }

  void make_hidden()
  {
    type.set(ID_C_hide, true);
  }

  goto_functiont()
  {
  }

  void clear()
  {
    body.clear();
    type.clear();
    parameter_identifiers.clear();
  }

  /// update the function member in each instruction
  /// \param function_id: the `function_id` used for assigning empty function
  ///   members
  void update_instructions_function(const irep_idt &function_id)
  {
    body.update_instructions_function(function_id);
  }

  void swap(goto_functiont &other)
  {
    body.swap(other.body);
    type.swap(other.type);
    parameter_identifiers.swap(other.parameter_identifiers);
  }

  void copy_from(const goto_functiont &other)
  {
    body.copy_from(other.body);
    type=other.type;
    parameter_identifiers=other.parameter_identifiers;
  }

  goto_functiont(const goto_functiont &)=delete;
  goto_functiont &operator=(const goto_functiont &)=delete;

  goto_functiont(goto_functiont &&other):
    body(std::move(other.body)),
    type(std::move(other.type)),
    parameter_identifiers(std::move(other.parameter_identifiers))
  {
  }

  goto_functiont &operator=(goto_functiont &&other)
  {
    body=std::move(other.body);
    type=std::move(other.type);
    parameter_identifiers=std::move(other.parameter_identifiers);
    return *this;
  }
};

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

  void unload(const irep_idt &name) { function_map.erase(name); }

  void clear()
  {
    function_map.clear();
  }

  void output(
    const namespacet &ns,
    std::ostream &out) const;

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
};

#define Forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::iterator \
      it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

#define forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::const_iterator \
      it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

void get_local_identifiers(
  const goto_functiont &,
  std::set<irep_idt> &dest);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H
