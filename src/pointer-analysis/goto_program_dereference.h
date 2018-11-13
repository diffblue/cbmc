/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H

#include <util/namespace.h>

#include <goto-programs/goto_model.h>

#include "value_sets.h"
#include "value_set_dereference.h"

/// Wrapper for functions removing dereferences in expressions contained in
/// a goto program.
class goto_program_dereferencet:protected dereference_callbackt
{
public:
  // Note: this currently doesn't specify a source language
  // for the final argument to value_set_dereferencet.
  // This means that language-inappropriate values such as
  // (struct A*)some_integer_value in Java, may be returned.
  goto_program_dereferencet(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    const optionst &_options,
    value_setst &_value_sets)
    : options(_options),
      ns(_ns),
      value_sets(_value_sets),
      dereference(_ns, _new_symbol_table, *this, ID_nil, false)
  {
  }

  void dereference_program(
    goto_programt &goto_program,
    bool checks_only=false);

  void dereference_program(
    goto_functionst &goto_functions,
    bool checks_only=false);

  void pointer_checks(goto_programt &goto_program);
  void pointer_checks(goto_functionst &goto_functions);

  void dereference_expression(
    goto_programt::const_targett target,
    exprt &expr);

  virtual ~goto_program_dereferencet()
  {
  }

protected:
  const optionst &options;
  const namespacet &ns;
  value_setst &value_sets;
  value_set_dereferencet dereference;

  DEPRECATED("Unused")
  virtual bool is_valid_object(const irep_idt &identifier);

  virtual bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol);

  DEPRECATED("Unused")
  virtual void dereference_failure(
    const std::string &property,
    const std::string &msg,
    const guardt &guard);

  virtual void get_value_set(const exprt &expr, value_setst::valuest &dest);

  void dereference_instruction(
    goto_programt::targett target,
    bool checks_only=false);

protected:
  void dereference_rec(
    exprt &expr, guardt &guard, const value_set_dereferencet::modet mode);
  void dereference_expr(
    exprt &expr,
    const bool checks_only,
    const value_set_dereferencet::modet mode);

#if 0
  const std::set<irep_idt> *valid_local_variables;
#endif
  goto_programt::const_targett current_target;

  /// Unused
  source_locationt dereference_location;

  /// Unused
  std::set<exprt> assertions;

  /// Unused
  goto_programt new_code;
};

void dereference(
  goto_programt::const_targett target,
  exprt &expr,
  const namespacet &,
  value_setst &);

void remove_pointers(
  goto_modelt &,
  value_setst &);

DEPRECATED("Unused")
void remove_pointers(
  goto_functionst &,
  symbol_tablet &,
  value_setst &);

DEPRECATED("Unused")
void pointer_checks(
  goto_programt &,
  symbol_tablet &,
  const optionst &,
  value_setst &);

DEPRECATED("Unused")
void pointer_checks(
  goto_functionst &,
  symbol_tablet &,
  const optionst &,
  value_setst &);

#endif // CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H
