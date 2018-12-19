/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_ALLOCATE_OBJECTS_H
#define CPROVER_UTIL_ALLOCATE_OBJECTS_H

#include "base_type.h"
#include "expr.h"
#include "namespace.h"
#include "source_location.h"
#include "std_code.h"
#include "symbol_table.h"
#include "type.h"

/// Selects the kind of objects allocated
enum class lifetimet
{
  /// Allocate local objects with automatic lifetime
  AUTOMATIC_LOCAL,
  /// Allocate global objects with static lifetime
  STATIC_GLOBAL,
  /// Allocate dynamic objects (using ALLOCATE)
  DYNAMIC
};

class allocate_objectst
{
public:
  allocate_objectst(
    const irep_idt &symbol_mode,
    const source_locationt &source_location,
    const irep_idt &name_prefix,
    symbol_table_baset &symbol_table)
    : symbol_mode(symbol_mode),
      source_location(source_location),
      name_prefix(name_prefix),
      symbol_table(symbol_table),
      ns(symbol_table)
  {
  }

  exprt allocate_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const lifetimet lifetime,
    const irep_idt &basename_prefix = "tmp");

  exprt allocate_automatic_local_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const irep_idt &basename_prefix = "tmp");

  exprt allocate_static_global_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const irep_idt &basename_prefix = "tmp");

  exprt allocate_dynamic_object(
    code_blockt &output_code,
    const exprt &target_expr,
    const typet &allocate_type);

  symbol_exprt allocate_automatic_local_object(
    const typet &allocate_type,
    const irep_idt &basename_prefix = "tmp");

  void add_created_symbol(const symbolt *symbol_ptr);

  void declare_created_symbols(code_blockt &init_code);

  void mark_created_symbols_as_input(code_blockt &init_code);

private:
  const irep_idt &symbol_mode;
  const source_locationt &source_location;
  const irep_idt &name_prefix;

  symbol_table_baset &symbol_table;
  const namespacet ns;

  std::vector<const symbolt *> symbols_created;

  exprt allocate_non_dynamic_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const bool static_lifetime,
    const irep_idt &basename_prefix);
};

#endif // CPROVER_UTIL_ALLOCATE_OBJECTS_H
