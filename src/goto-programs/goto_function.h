/*******************************************************************\

Module: A GOTO Function

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Goto Function

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_H

#include <iosfwd>

#include <util/std_types.h>

#include "goto_program.h"

/// A goto function, consisting of function type (see #type), function body (see
/// #body), and parameter identifiers (see #parameter_identifiers).
class goto_functiont
{
public:
  goto_programt body;

  /// The type of the function, indicating the return type and parameter types
  code_typet type;

  typedef std::vector<irep_idt> parameter_identifierst;

  /// The identifiers of the parameters of this function
  ///
  /// Note: This variable is currently unused and the vector is thus always
  /// empty. In the future the code base may be refactored to fill in the
  /// parameter identifiers here when creating a `goto_functiont`. For now the
  /// parameter identifiers should be retrieved from the type (`code_typet`).
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

  goto_functiont() : body(), type({}, empty_typet())
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
    type = other.type;
    parameter_identifiers = other.parameter_identifiers;
  }

  goto_functiont(const goto_functiont &) = delete;
  goto_functiont &operator=(const goto_functiont &) = delete;

  goto_functiont(goto_functiont &&other)
    : body(std::move(other.body)),
      type(std::move(other.type)),
      parameter_identifiers(std::move(other.parameter_identifiers))
  {
  }

  goto_functiont &operator=(goto_functiont &&other)
  {
    body = std::move(other.body);
    type = std::move(other.type);
    parameter_identifiers = std::move(other.parameter_identifiers);
    return *this;
  }

  bool
  check_internal_invariants(const symbol_tablet &table, messaget &msg) const
  {
    return body.check_internal_invariants(table, msg);
  }
};

void get_local_identifiers(const goto_functiont &, std::set<irep_idt> &dest);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_H
