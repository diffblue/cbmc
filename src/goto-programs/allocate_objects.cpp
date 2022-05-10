/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "allocate_objects.h"

#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/symbol.h>

#include "goto_instruction_code.h"

/// Allocates a new object, either by creating a local variable with automatic
/// lifetime, a global variable with static lifetime, or by dynamically
/// allocating memory via ALLOCATE(). Code is added to `assignments` which
/// assigns a pointer to the allocated memory to `target_expr`. The
/// `allocate_type` may differ from `target_expr.type()`, e.g. for target_expr
/// having type `int*` and `allocate_type` being an `int[10]`.
///
/// \param assignments: The code block to add code to.
/// \param target_expr: A pointer to the allocated memory will be assigned to
///   this lvalue expression
/// \param allocate_type: Type of the object allocated
/// \param lifetime: Lifetime of the allocated object (AUTOMATIC_LOCAL,
///   STATIC_GLOBAL, or DYNAMIC)
/// \param basename_prefix: prefix of the basename of the new variable
/// \return An lvalue expression denoting the newly allocated object
exprt allocate_objectst::allocate_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const lifetimet lifetime,
  const irep_idt &basename_prefix)
{
  switch(lifetime)
  {
  case lifetimet::AUTOMATIC_LOCAL:
    return allocate_automatic_local_object(
      assignments, target_expr, allocate_type, basename_prefix);
    break;

  case lifetimet::STATIC_GLOBAL:
    return allocate_static_global_object(
      assignments, target_expr, allocate_type, basename_prefix);
    break;

  case lifetimet::DYNAMIC:
    return allocate_dynamic_object(assignments, target_expr, allocate_type);
    break;
  }

  UNREACHABLE;
}

/// Creates a local variable with automatic lifetime. Code is added to
/// `assignments` which assigns a pointer to the variable to `target_expr`. The
/// `allocate_type` may differ from `target_expr.type()`, e.g. for `target_expr`
/// having type `int*` and `allocate_type` being an `int[10]`..
///
/// \param assignments: The code block to add code to.
/// \param target_expr: A pointer to the variable will be assigned to this
///   lvalue expression
/// \param allocate_type: Type of the new variable
/// \param basename_prefix: prefix of the basename of the new variable
/// \return An expression denoting the variable
exprt allocate_objectst::allocate_automatic_local_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const irep_idt &basename_prefix)
{
  return allocate_non_dynamic_object(
    assignments, target_expr, allocate_type, false, basename_prefix);
}

/// Creates a global variable with static lifetime. Code is added to
/// `assignments` which assigns a pointer to the variable to `target_expr`. The
/// `allocate_type` may differ from `target_expr.type()`, e.g. for `target_expr`
/// having type `int*` and `allocate_type` being an `int[10]`.
///
/// \param assignments: The code block to add code to.
/// \param target_expr: A pointer to the variable will be assigned to this
///   lvalue expression
/// \param allocate_type: Type of the new variable
/// \param basename_prefix: prefix of the basename of the new variable
/// \return An expression denoting the variable
exprt allocate_objectst::allocate_static_global_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const irep_idt &basename_prefix)
{
  return allocate_non_dynamic_object(
    assignments, target_expr, allocate_type, true, basename_prefix);
}

/// Creates a local variable with automatic lifetime and returns it as a symbol
/// expression.
///
/// \param allocate_type: Type of the new variable
/// \param basename_prefix: prefix of the basename of the new variable
/// \return A symbol expression denoting the variable
symbol_exprt allocate_objectst::allocate_automatic_local_object(
  const typet &allocate_type,
  const irep_idt &basename_prefix)
{
  symbolt &aux_symbol = get_fresh_aux_symbol(
    allocate_type,
    id2string(name_prefix),
    id2string(basename_prefix),
    source_location,
    symbol_mode,
    symbol_table);

  add_created_symbol(aux_symbol);

  return aux_symbol.symbol_expr();
}

exprt allocate_objectst::allocate_dynamic_object_symbol(
  code_blockt &output_code,
  const exprt &target_expr,
  const typet &allocate_type)
{
  if(allocate_type.id() == ID_empty)
  {
    // make null
    code_frontend_assignt code{
      target_expr,
      null_pointer_exprt{to_pointer_type(target_expr.type())},
      source_location};
    output_code.add(std::move(code));

    return exprt();
  }

  // build size expression
  auto object_size = size_of_expr(allocate_type, ns);
  INVARIANT(object_size.has_value(), "Size of objects should be known");

  // create a symbol for the malloc expression so we can initialize
  // without having to do it potentially through a double-deref, which
  // breaks the to-SSA phase.
  symbolt &malloc_sym = get_fresh_aux_symbol(
    pointer_type(allocate_type),
    id2string(name_prefix),
    "malloc_site",
    source_location,
    symbol_mode,
    symbol_table);

  add_created_symbol(malloc_sym);

  code_frontend_assignt assign =
    make_allocate_code(malloc_sym.symbol_expr(), object_size.value());
  output_code.add(assign);

  exprt malloc_symbol_expr = typecast_exprt::conditional_cast(
    malloc_sym.symbol_expr(), target_expr.type());

  code_frontend_assignt code(target_expr, malloc_symbol_expr);
  code.add_source_location() = source_location;
  output_code.add(code);

  return malloc_sym.symbol_expr();
}

exprt allocate_objectst::allocate_dynamic_object(
  code_blockt &output_code,
  const exprt &target_expr,
  const typet &allocate_type)
{
  return dereference_exprt(
    allocate_dynamic_object_symbol(output_code, target_expr, allocate_type));
}

exprt allocate_objectst::allocate_non_dynamic_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const bool static_lifetime,
  const irep_idt &basename_prefix)
{
  symbolt &aux_symbol = get_fresh_aux_symbol(
    allocate_type,
    id2string(name_prefix),
    id2string(basename_prefix),
    source_location,
    symbol_mode,
    symbol_table);

  aux_symbol.is_static_lifetime = static_lifetime;
  add_created_symbol(aux_symbol);

  exprt aoe = typecast_exprt::conditional_cast(
    address_of_exprt(aux_symbol.symbol_expr()), target_expr.type());

  code_frontend_assignt code(target_expr, aoe);
  code.add_source_location() = source_location;
  assignments.add(code);

  if(aoe.id() == ID_typecast)
  {
    return dereference_exprt(aoe);
  }
  else
  {
    return aux_symbol.symbol_expr();
  }
}

/// Add a pointer to a symbol to the list of pointers to symbols created so far
///
/// \param symbol: symbol in the symbol table
void allocate_objectst::add_created_symbol(const symbolt &symbol)
{
  symbols_created.push_back(symbol.name);
}

/// Adds declarations for all non-static symbols created
///
/// \param init_code: code block to which to add the declarations
void allocate_objectst::declare_created_symbols(code_blockt &init_code)
{
  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const auto &symbol_id : symbols_created)
  {
    const symbolt &symbol = ns.lookup(symbol_id);
    if(!symbol.is_static_lifetime)
    {
      code_frontend_declt decl{symbol.symbol_expr()};
      decl.add_source_location() = source_location;
      init_code.add(decl);
    }
  }
}

/// Adds code to mark the created symbols as input
///
/// \param init_code: code block to which to add the generated code
void allocate_objectst::mark_created_symbols_as_input(code_blockt &init_code)
{
  // Add the following code to init_code for each symbol that's been created:
  //   INPUT("<identifier>", <identifier>);
  for(const auto &symbol_id : symbols_created)
  {
    const symbolt &symbol = ns.lookup(symbol_id);
    init_code.add(
      code_inputt{symbol.base_name, symbol.symbol_expr(), source_location});
  }
}

code_frontend_assignt
make_allocate_code(const symbol_exprt &lhs, const exprt &size)
{
  side_effect_exprt alloc{
    ID_allocate, {size, false_exprt()}, lhs.type(), lhs.source_location()};
  return code_frontend_assignt(lhs, alloc);
}
