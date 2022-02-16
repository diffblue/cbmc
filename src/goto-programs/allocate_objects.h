/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_ALLOCATE_OBJECTS_H
#define CPROVER_UTIL_ALLOCATE_OBJECTS_H

#include "goto_instruction_code.h"

#include <util/namespace.h>
#include <util/source_location.h>
#include <util/std_code.h>

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

  /// Generates code for allocating a dynamic object. A new variable with
  /// basename prefix `alloc_site` is introduced to which the allocated memory
  /// is assigned.
  /// Then, the variable is assigned to `target_expr`. For example, with
  /// `target_expr` being `*p` the following code is generated:
  ///
  /// `alloc_site$1 = ALLOCATE(object_size, FALSE);`
  /// `*p = alloc_site$1;`
  ///
  /// \param output_code: Code block to which the necessary code is added
  /// \param target_expr: A pointer to the allocated memory will be assigned to
  ///   this (lvalue) expression
  /// \param allocate_type: Type of the object allocated
  /// \return The pointer to the allocated memory, or an empty expression
  ///   when `allocate_type` is void
  exprt allocate_dynamic_object_symbol(
    code_blockt &output_code,
    const exprt &target_expr,
    const typet &allocate_type);

  /// Generate the same code as \ref allocate_dynamic_object_symbol, but
  /// return a dereference_exprt that dereferences the newly created pointer
  /// to the allocated memory.
  exprt allocate_dynamic_object(
    code_blockt &output_code,
    const exprt &target_expr,
    const typet &allocate_type);

  symbol_exprt allocate_automatic_local_object(
    const typet &allocate_type,
    const irep_idt &basename_prefix = "tmp");

  void add_created_symbol(const symbolt &symbol);

  void declare_created_symbols(code_blockt &init_code);

  void mark_created_symbols_as_input(code_blockt &init_code);

private:
  const irep_idt symbol_mode;
  const source_locationt source_location;
  const irep_idt name_prefix;

  symbol_table_baset &symbol_table;
  const namespacet ns;

  std::vector<irep_idt> symbols_created;

  exprt allocate_non_dynamic_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const bool static_lifetime,
    const irep_idt &basename_prefix);
};

/// Create code allocating an object of size `size` and assigning it to `lhs`
/// \param lhs: pointer which will be allocated
/// \param size: size of the object
/// \return code allocating the object and assigning it to `lhs`
code_frontend_assignt
make_allocate_code(const symbol_exprt &lhs, const exprt &size);

#endif // CPROVER_UTIL_ALLOCATE_OBJECTS_H
