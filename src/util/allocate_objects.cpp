/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "allocate_objects.h"

#include "arith_tools.h"
#include "c_types.h"
#include "fresh_symbol.h"
#include "pointer_offset_size.h"
#include "string_constant.h"
#include "type_eq.h"

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

  symbols_created.push_back(&aux_symbol);

  return aux_symbol.symbol_expr();
}

/// Generates code for allocating a dynamic object. A new variable with basename
/// prefix `alloc_site` is introduced to which the allocated memory is assigned.
/// Then, the variable is assigned to `target_expr`. For example, with
/// `target_expr` being `*p` the following code is generated:
///
/// `alloc_site$1 = ALLOCATE(object_size, FALSE);`
/// `*p = alloc_site$1;`
///
/// The function returns a dereference expressiont that dereferences the
/// allocation site variable (e.g., `*alloc_site$1`) and which can be used to
/// initialize the allocated memory.
///
/// \param output_code: Code block to which the necessary code is added
/// \param target_expr: A pointer to the allocated memory will be assigned to
///   this (lvalue) expression
/// \param allocate_type: Type of the object allocated
/// \return A dereference_exprt that dereferences the pointer to the allocated
///   memory, or an empty expression when `allocate_type` is void
exprt allocate_objectst::allocate_dynamic_object(
  code_blockt &output_code,
  const exprt &target_expr,
  const typet &allocate_type)
{
  if(allocate_type.id() == ID_empty)
  {
    // make null
    null_pointer_exprt null_pointer_expr(to_pointer_type(target_expr.type()));
    code_assignt code(target_expr, null_pointer_expr);
    code.add_source_location() = source_location;
    output_code.add(code);

    return exprt();
  }

  // build size expression
  exprt object_size = size_of_expr(allocate_type, ns);
  INVARIANT(!object_size.is_nil(), "Size of objects should be known");

  // malloc expression
  side_effect_exprt malloc_expr(
    ID_allocate, pointer_type(allocate_type), source_location);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.copy_to_operands(false_exprt());

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

  symbols_created.push_back(&malloc_sym);

  code_assignt assign(malloc_sym.symbol_expr(), malloc_expr);
  assign.add_source_location() = source_location;
  output_code.add(assign);

  exprt malloc_symbol_expr =
    !type_eq(malloc_sym.symbol_expr().type(), target_expr.type(), ns)
      ? (exprt)typecast_exprt(malloc_sym.symbol_expr(), target_expr.type())
      : malloc_sym.symbol_expr();

  code_assignt code(target_expr, malloc_symbol_expr);
  code.add_source_location() = source_location;
  output_code.add(code);

  return dereference_exprt(malloc_sym.symbol_expr());
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
  symbols_created.push_back(&aux_symbol);

  exprt aoe = typecast_exprt::conditional_cast(
    address_of_exprt(aux_symbol.symbol_expr()), target_expr.type());

  code_assignt code(target_expr, aoe);
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
/// \param symbol_ptr: pointer to a symbol in the symbol table
void allocate_objectst::add_created_symbol(const symbolt *symbol_ptr)
{
  symbols_created.push_back(symbol_ptr);
}

/// Adds declarations for all non-static symbols created
///
/// \param init_code: code block to which to add the declarations
void allocate_objectst::declare_created_symbols(code_blockt &init_code)
{
  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt *const symbol_ptr : symbols_created)
  {
    if(!symbol_ptr->is_static_lifetime)
    {
      code_declt decl(symbol_ptr->symbol_expr());
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
  for(symbolt const *symbol_ptr : symbols_created)
  {
    codet input_code(ID_input);
    input_code.operands().resize(2);
    input_code.op0() = address_of_exprt(index_exprt(
      string_constantt(symbol_ptr->base_name), from_integer(0, index_type())));
    input_code.op1() = symbol_ptr->symbol_expr();
    input_code.add_source_location() = source_location;
    init_code.add(std::move(input_code));
  }
}
