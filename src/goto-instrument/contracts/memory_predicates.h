/*******************************************************************\

Module: Predicates to specify memory footprint in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Predicates to specify memory footprint in function contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_MEMORY_PREDICATES_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_MEMORY_PREDICATES_H

#include "contracts.h"

class is_fresh_baset
{
public:
  is_fresh_baset(
    code_contractst &_parent,
    messaget _log,
    const irep_idt _fun_id)
    : parent(_parent), log(_log), fun_id(_fun_id)
  {
  }

  void update_requires(goto_programt &requires);
  void update_ensures(goto_programt &ensures);

  virtual void create_declarations() = 0;

  void add_memory_map_decl(goto_programt &program);
  void add_memory_map_dead(goto_programt &program);

protected:
  void add_declarations(const std::string &decl_string);
  void update_fn_call(
    goto_programt::targett &target,
    const std::string &name,
    bool add_address_of);

  virtual void create_requires_fn_call(goto_programt::targett &target) = 0;
  virtual void create_ensures_fn_call(goto_programt::targett &target) = 0;

  code_contractst &parent;
  messaget log;
  irep_idt fun_id;

  // written by the child classes.
  std::string memmap_name;
  std::string requires_fn_name;
  std::string ensures_fn_name;
  symbolt memmap_symbol;

  array_typet get_memmap_type();
};

class is_fresh_enforcet : public is_fresh_baset
{
public:
  is_fresh_enforcet(
    code_contractst &_parent,
    messaget _log,
    const irep_idt _fun_id);

  virtual void create_declarations();

protected:
  virtual void create_requires_fn_call(goto_programt::targett &target);
  virtual void create_ensures_fn_call(goto_programt::targett &target);
};

class is_fresh_replacet : public is_fresh_baset
{
public:
  is_fresh_replacet(
    code_contractst &_parent,
    messaget _log,
    const irep_idt _fun_id);

  virtual void create_declarations();

protected:
  virtual void create_requires_fn_call(goto_programt::targett &target);
  virtual void create_ensures_fn_call(goto_programt::targett &target);
};

/// Predicate to be used with the exprt::visit() function.  It
/// will return the set of function calls within a goto program.
class find_is_fresh_calls_visitort
{
public:
  find_is_fresh_calls_visitort()
  {
  }

  // \brief return the set of functions invoked by
  // the call graph of this program.
  std::set<goto_programt::targett> &is_fresh_calls();
  void clear_set();
  void operator()(goto_programt &prog);

protected:
  std::set<goto_programt::targett> function_set;
};

/// Predicate to be used with the exprt::visit() function. The function
/// found_return_value() will return `true` iff this predicate is called on an
/// expr that contains `__CPROVER_return_value`.
class functions_in_scope_visitort
{
public:
  functions_in_scope_visitort(
    const goto_functionst &goto_functions,
    messaget &log)
    : goto_functions(goto_functions), log(log)
  {
  }

  // \brief return the set of functions invoked by
  // the call graph of this program.
  std::set<irep_idt> &function_calls();
  void operator()(const goto_programt &prog);

protected:
  const goto_functionst &goto_functions;
  messaget &log;
  std::set<irep_idt> function_set;
};

class function_binding_visitort : const_expr_visitort
{
public:
  function_binding_visitort() : const_expr_visitort()
  {
  }

  void operator()(const exprt &exp) override
  {
  }
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_MEMORY_PREDICATES_H
