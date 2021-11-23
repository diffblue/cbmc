/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#ifndef CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H

#include <util/message.h>

#include "dereference_callback.h"
#include "value_set_dereference.h"

class exprt;
class goto_functionst;
class goto_modelt;
class namespacet;
class optionst;
class symbol_tablet;
class symbolt;
class value_setst;

/// Wrapper for functions removing dereferences in expressions contained in
/// a goto program.
class goto_program_dereferencet:protected dereference_callbackt
{
public:
  // Note: this currently doesn't specify a source language
  // for the final argument to value_set_dereferencet.
  // This means that language-inappropriate values such as
  // (struct A*)some_integer_value in Java, may be returned.
  // Note: value_set_dereferencet requires a messaget instance
  // as on of its arguments to display the points-to set
  // during symex. Display is not done during goto-program
  // conversion. To ensure this the display_points_to_sets
  // parameter in value_set_dereferencet::dereference()
  // is set to false by default and is not changed by the
  // goto program conversion modules. Similarly, here we set
  // _log to be a default messaget instance.
  goto_program_dereferencet(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    const optionst &_options,
    value_setst &_value_sets,
    const messaget &_log = messaget())
    : options(_options),
      ns(_ns),
      value_sets(_value_sets),
      dereference(_ns, _new_symbol_table, *this, ID_nil, false, _log)
  {
  }

  void dereference_program(
    goto_programt &goto_program,
    bool checks_only=false);

  void dereference_program(
    goto_functionst &goto_functions,
    bool checks_only=false);

  void dereference_expression(
    const irep_idt &function_id,
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

  const symbolt *get_or_create_failed_symbol(const exprt &expr) override;

  std::vector<exprt> get_value_set(const exprt &expr) const override;

  void dereference_instruction(
    goto_programt::targett target,
    bool checks_only=false);

protected:
  void dereference_rec(exprt &expr);
  void dereference_expr(exprt &expr, const bool checks_only);

  irep_idt current_function;
  goto_programt::const_targett current_target;
  goto_programt new_code;
};

void dereference(
  const irep_idt &function_id,
  goto_programt::const_targett target,
  exprt &expr,
  const namespacet &,
  value_setst &);

void remove_pointers(
  goto_modelt &,
  value_setst &);

#define OPT_REMOVE_POINTERS "(remove-pointers)"

// clang-format off
#define HELP_REMOVE_POINTERS                                                   \
  " --remove-pointers            converts pointer arithmetic to base+offset expressions\n" /* NOLINT(whitespace/line_length) */

// clang-format on

#endif // CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H
