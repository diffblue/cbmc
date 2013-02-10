/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_GOTO_PROGRAM_DEREFERENCE_H

#include <namespace.h>
#include <goto-programs/goto_functions.h>

#include "value_sets.h"
#include "dereference.h"

class goto_program_dereferencet:protected dereference_callbackt
{
public:
  goto_program_dereferencet(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    const optionst &_options,
    value_setst &_value_sets):
    options(_options),
    ns(_ns),
    value_sets(_value_sets),
    dereference(_ns, _new_symbol_table, _options, *this) { }

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
  dereferencet dereference;

  virtual bool is_valid_object(const irep_idt &identifier);

  virtual bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol);

  virtual void dereference_failure(
    const std::string &property,
    const std::string &msg,
    const guardt &guard);

  virtual void get_value_set(const exprt &expr, value_setst::valuest &dest);

  void dereference_instruction(
    goto_programt::targett target,
    bool checks_only=false);

protected:
  void dereference_rec(exprt &expr, guardt &guard, const dereferencet::modet mode);
  void dereference_expr(exprt &expr, const bool checks_only, const dereferencet::modet mode);
  
  const std::set<irep_idt> *valid_local_variables;
  locationt dereference_location;
  goto_programt::const_targett current_target;
  
  std::set<exprt> assertions;
  goto_programt new_code;
};

void dereference(
  goto_programt::const_targett target,
  exprt &expr,
  const namespacet &ns,
  value_setst &value_sets);

void remove_pointers(
  goto_programt &goto_program,
  symbol_tablet &symbol_table,
  value_setst &value_sets);

void remove_pointers(
  goto_functionst &goto_functions,
  symbol_tablet &symbol_table,
  value_setst &value_sets);

void pointer_checks(
  goto_programt &goto_program,
  symbol_tablet &symbol_table,
  const optionst &options,
  value_setst &value_sets);

void pointer_checks(
  goto_functionst &goto_functions,
  symbol_tablet &symbol_table,
  const optionst &options,
  value_setst &value_sets);

#endif
