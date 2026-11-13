/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#ifndef CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H
#define CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H

#include "allocate_objects.h"

#include <set>

class message_handlert;

struct c_object_factory_parameterst;

class symbol_factoryt
{
  symbol_table_baset &symbol_table;
  const source_locationt &loc;
  namespacet ns;
  const c_object_factory_parameterst &object_factory_params;

  allocate_objectst allocate_objects;

  const lifetimet lifetime;

  /// Number of dynamic objects this factory has allocated.  A fresh
  /// `symbol_factoryt` is constructed for each nondet-init root, so comparing
  /// this with `object_factory_params.max_dynamic_object_instances` limits
  /// the number of objects per root.
  std::size_t dynamic_object_instance_count = 0;

  /// Whether a pointer was initialised to NULL because of
  /// `object_factory_params.max_dynamic_object_instances`.
  bool dynamic_object_limit_reached = false;

public:
  typedef std::set<irep_idt> recursion_sett;

  symbol_factoryt(
    symbol_table_baset &_symbol_table,
    const source_locationt &loc,
    const irep_idt &name_prefix,
    const c_object_factory_parameterst &object_factory_params,
    const lifetimet lifetime)
    : symbol_table(_symbol_table),
      loc(loc),
      ns(_symbol_table),
      object_factory_params(object_factory_params),
      allocate_objects(ID_C, loc, name_prefix, symbol_table),
      lifetime(lifetime)
  {
  }

  void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    const std::size_t depth = 0,
    recursion_sett recursion_set = recursion_sett(),
    const bool assign_const = true);

  /// Whether any pointer was initialised to NULL, rather than to a fresh
  /// object, because the limit on the number of dynamic objects
  /// (`--max-dynamic-object-instances`) was reached.
  bool limit_reached() const
  {
    return dynamic_object_limit_reached;
  }

  /// Warn, via \p message_handler, if limit_reached().
  void warn_if_limit_reached(message_handlert &message_handler) const;

  void add_created_symbol(const symbolt &symbol)
  {
    allocate_objects.add_created_symbol(symbol);
  }

  void declare_created_symbols(code_blockt &init_code)
  {
    allocate_objects.declare_created_symbols(init_code);
  }

  void mark_created_symbols_as_input(code_blockt &init_code)
  {
    allocate_objects.mark_created_symbols_as_input(init_code);
  }

private:
  /// Generate initialisation code for each array element
  /// \param assignments: The code block to add code to
  /// \param expr: An expression of array type
  /// \param depth: The struct recursion depth
  /// \param recursion_set: The struct recursion set
  /// \see gen_nondet_init For the meaning of the last 2 parameters
  void gen_nondet_array_init(
    code_blockt &assignments,
    const exprt &expr,
    std::size_t depth,
    const recursion_sett &recursion_set);
};

symbol_exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &,
  const c_object_factory_parameterst &object_factory_parameters,
  const lifetimet lifetime,
  message_handlert &message_handler);

#endif // CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H
