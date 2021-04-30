/*******************************************************************\

Module: A GOTO Function

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Goto Function

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_H

#include <util/std_types.h>

#include "goto_program.h"

/// A goto function, consisting of function body (see #body) and parameter
/// identifiers (see #parameter_identifiers).
class goto_functiont
{
public:
  goto_programt body;

  typedef std::vector<irep_idt> parameter_identifierst;
  /// The identifiers of the parameters of this function
  ///
  /// Note: This is now the preferred way of getting the identifiers of the
  /// parameters. The identifiers in the type will go away.
  parameter_identifierst parameter_identifiers;

  bool body_available() const
  {
    return !body.instructions.empty();
  }

  void set_parameter_identifiers(const code_typet &code_type)
  {
    parameter_identifiers.clear();
    parameter_identifiers.reserve(code_type.parameters().size());
    for(const auto &parameter : code_type.parameters())
      parameter_identifiers.push_back(parameter.get_identifier());
  }

  bool is_hidden() const
  {
    return function_is_hidden;
  }

  void make_hidden()
  {
    function_is_hidden = true;
  }

  goto_functiont() : body(), function_is_hidden(false)
  {
  }

  void clear()
  {
    body.clear();
    parameter_identifiers.clear();
    function_is_hidden = false;
  }

  void swap(goto_functiont &other)
  {
    body.swap(other.body);
    parameter_identifiers.swap(other.parameter_identifiers);
    std::swap(function_is_hidden, other.function_is_hidden);
  }

  void copy_from(const goto_functiont &other)
  {
    body.copy_from(other.body);
    parameter_identifiers = other.parameter_identifiers;
    function_is_hidden = other.function_is_hidden;
  }

  goto_functiont(const goto_functiont &) = delete;
  goto_functiont &operator=(const goto_functiont &) = delete;

  goto_functiont(goto_functiont &&other)
    : body(std::move(other.body)),
      parameter_identifiers(std::move(other.parameter_identifiers)),
      function_is_hidden(other.function_is_hidden)
  {
  }

  goto_functiont &operator=(goto_functiont &&other)
  {
    body = std::move(other.body);
    parameter_identifiers = std::move(other.parameter_identifiers);
    function_is_hidden = other.function_is_hidden;
    return *this;
  }

  /// Check that the goto function is well-formed
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  void validate(const namespacet &ns, const validation_modet vm) const;

protected:
  bool function_is_hidden;
};

void get_local_identifiers(const goto_functiont &, std::set<irep_idt> &dest);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_H
