/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#ifndef CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H
#define CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H

#include "c_object_factory_parameters.h"

#include <set>
#include <vector>

#include <util/allocate_objects.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

class symbol_factoryt
{
  symbol_tablet &symbol_table;
  const source_locationt &loc;
  namespacet ns;
  const c_object_factory_parameterst &object_factory_params;

  allocate_objectst allocate_objects;

  const lifetimet lifetime;

public:
  typedef std::set<irep_idt> recursion_sett;

  symbol_factoryt(
    symbol_tablet &_symbol_table,
    const source_locationt &loc,
    const c_object_factory_parameterst &object_factory_params,
    const lifetimet lifetime)
    : symbol_table(_symbol_table),
      loc(loc),
      ns(_symbol_table),
      object_factory_params(object_factory_params),
      allocate_objects(ID_C, loc, loc.get_function(), symbol_table),
      lifetime(lifetime)
  {
  }

  void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    const std::size_t depth = 0,
    recursion_sett recursion_set = recursion_sett(),
    const bool assign_const = true);

  void add_created_symbol(const symbolt *symbol_ptr)
  {
    allocate_objects.add_created_symbol(symbol_ptr);
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
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &,
  const c_object_factory_parameterst &object_factory_parameters,
  const lifetimet lifetime);

#endif // CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H
