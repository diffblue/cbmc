/*******************************************************************\

Module: Remove Java New Operators

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Remove Java New Operators

#include "remove_java_new.h"

#include <goto-programs/class_identifier.h>
#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_model.h>

#include "java_types.h"
#include "java_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>

class remove_java_newt
{
public:
  explicit remove_java_newt(symbol_table_baset &symbol_table)
    : symbol_table(symbol_table), ns(symbol_table)
  {
  }

  // Lower java_new for a single function
  bool lower_java_new(
    const irep_idt &function_identifier,
    goto_programt &,
    message_handlert &);

  // Lower java_new for a single instruction
  goto_programt::targett lower_java_new(
    const irep_idt &function_identifier,
    goto_programt &,
    goto_programt::targett,
    message_handlert &);

protected:
  symbol_table_baset &symbol_table;
  namespacet ns;

  goto_programt::targett lower_java_new(
    const irep_idt &function_identifier,
    const exprt &lhs,
    const side_effect_exprt &rhs,
    goto_programt &,
    goto_programt::targett);

  goto_programt::targett lower_java_new_array(
    const irep_idt &function_identifier,
    const exprt &lhs,
    const side_effect_exprt &rhs,
    goto_programt &,
    goto_programt::targett,
    message_handlert &);
};

/// Replaces the instruction `lhs = new java_type` by
/// two instructions:
///   lhs = ALLOCATE(java_type)
///   *lhs = { zero-initialized java_type }
/// \param function_identifier: Name of the function containing \p target.
/// \param lhs: the lhs
/// \param rhs: the rhs
/// \param dest: the goto program to modify
/// \param target: the goto instruction to replace
/// \return the iterator advanced to the last of the inserted instructions
/// Note: we have to take a copy of `lhs` and `rhs` since they would suffer
///   destruction when replacing the instruction.
goto_programt::targett remove_java_newt::lower_java_new(
  const irep_idt &function_identifier,
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest,
  goto_programt::targett target)
{
  PRECONDITION(!lhs.is_nil());
  PRECONDITION(rhs.operands().empty());
  PRECONDITION(rhs.type().id() == ID_pointer);
  source_locationt location = rhs.source_location();
  typet object_type = rhs.type().subtype();

  // build size expression
  const auto object_size = size_of_expr(object_type, ns);
  CHECK_RETURN(object_size.has_value());

  // we produce a malloc side-effect, which stays
  side_effect_exprt malloc_expr(ID_allocate, rhs.type(), location);
  malloc_expr.copy_to_operands(*object_size);
  // could use true and get rid of the code below
  malloc_expr.copy_to_operands(false_exprt());
  *target =
    goto_programt::make_assignment(code_assignt(lhs, malloc_expr), location);

  // zero-initialize the object
  dereference_exprt deref(lhs, object_type);
  auto zero_object = zero_initializer(object_type, location, ns);
  CHECK_RETURN(zero_object.has_value());
  set_class_identifier(
    to_struct_expr(*zero_object), ns, to_struct_tag_type(object_type));
  return dest.insert_after(
    target,
    goto_programt::make_assignment(
      code_assignt(deref, *zero_object), location));
}

/// Replaces the instruction `lhs = new java_array_type` by
/// the following code:
///   lhs = ALLOCATE(java_type)
///   loops to initialize the elements (including multi-dimensional arrays)
/// \param function_identifier: Name of the function containing \p target.
/// \param lhs: the lhs
/// \param rhs: the rhs
/// \param dest: the goto program to modify
/// \param target: the goto instruction to replace
/// \param message_handler: message handler
/// \return the iterator advanced to the last of the inserted instructions
/// Note: we have to take a copy of `lhs` and `rhs` since they would suffer
///   destruction when replacing the instruction.
goto_programt::targett remove_java_newt::lower_java_new_array(
  const irep_idt &function_identifier,
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest,
  goto_programt::targett target,
  message_handlert &message_handler)
{
  // lower_java_new_array without lhs not implemented
  PRECONDITION(!lhs.is_nil());
  PRECONDITION(rhs.operands().size() >= 1); // one per dimension
  PRECONDITION(rhs.type().id() == ID_pointer);

  source_locationt location = rhs.source_location();
  struct_tag_typet object_type = to_struct_tag_type(rhs.type().subtype());
  PRECONDITION(ns.follow(object_type).id() == ID_struct);

  // build size expression
  const auto object_size = size_of_expr(object_type, ns);
  CHECK_RETURN(object_size.has_value());

  // we produce a malloc side-effect, which stays
  side_effect_exprt malloc_expr(ID_allocate, rhs.type(), location);
  malloc_expr.copy_to_operands(*object_size);
  // code use true and get rid of the code below
  malloc_expr.copy_to_operands(false_exprt());

  *target =
    goto_programt::make_assignment(code_assignt(lhs, malloc_expr), location);
  goto_programt::targett next = std::next(target);

  const struct_typet &struct_type = to_struct_type(ns.follow(object_type));

  PRECONDITION(is_valid_java_array(struct_type));

  // Init base class:
  dereference_exprt deref(lhs, object_type);
  auto zero_object = zero_initializer(object_type, location, ns);
  CHECK_RETURN(zero_object.has_value());
  set_class_identifier(to_struct_expr(*zero_object), ns, object_type);
  dest.insert_before(
    next,
    goto_programt::make_assignment(
      code_assignt(deref, *zero_object), location));

  // If it's a reference array we need to set the dimension and element type
  // fields. Primitive array types don't have these fields; if the element type
  // is a void pointer then the element type is statically unknown and the
  // caller must set these up itself. This happens in array[reference].clone(),
  // where the type info must be copied over from the input array)
  const auto underlying_type_and_dimension =
    java_array_dimension_and_element_type(object_type);

  bool target_type_is_reference_array =
    underlying_type_and_dimension.second >= 1 &&
    can_cast_type<java_reference_typet>(underlying_type_and_dimension.first);

  if(target_type_is_reference_array)
  {
    exprt object_array_dimension = get_array_dimension_field(lhs);
    dest.insert_before(
      next,
      goto_programt::make_assignment(code_assignt(
        object_array_dimension,
        from_integer(
          underlying_type_and_dimension.second, object_array_dimension.type()),
        location)));

    exprt object_array_element_type = get_array_element_type_field(lhs);
    dest.insert_before(
      next,
      goto_programt::make_assignment(code_assignt(
        object_array_element_type,
        constant_exprt(
          to_struct_tag_type(underlying_type_and_dimension.first.subtype())
            .get_identifier(),
          string_typet()),
        location)));
  }

  // if it's an array, we need to set the length field
  member_exprt length(
    deref,
    struct_type.components()[1].get_name(),
    struct_type.components()[1].type());
  dest.insert_before(
    next,
    goto_programt::make_assignment(
      code_assignt(length, to_multi_ary_expr(rhs).op0()), location));

  // we also need to allocate space for the data
  member_exprt data(
    deref,
    struct_type.components()[2].get_name(),
    struct_type.components()[2].type());

  // Allocate a (struct realtype**) instead of a (void**) if possible.
  const irept &given_element_type = object_type.find(ID_element_type);
  typet allocate_data_type;
  if(given_element_type.is_not_nil())
  {
    allocate_data_type =
      pointer_type(static_cast<const typet &>(given_element_type));
  }
  else
    allocate_data_type = data.type();

  side_effect_exprt data_java_new_expr(
    ID_java_new_array_data, allocate_data_type, location);

  // The instruction may specify a (hopefully small) upper bound on the
  // array size, in which case we allocate a fixed-length array that may
  // be larger than the `length` member rather than use a true variable-
  // length array, which produces a more complex formula in the current
  // backend.
  const irept size_bound = rhs.find(ID_length_upper_bound);
  if(size_bound.is_nil())
    data_java_new_expr.set(ID_size, to_multi_ary_expr(rhs).op0());
  else
    data_java_new_expr.set(ID_size, size_bound);

  // Must directly assign the new array to a temporary
  // because goto-symex will notice `x=side_effect_exprt` but not
  // `x=typecast_exprt(side_effect_exprt(...))`
  symbol_exprt new_array_data_symbol = fresh_java_symbol(
                                         data_java_new_expr.type(),
                                         "tmp_new_data_array",
                                         location,
                                         function_identifier,
                                         symbol_table)
                                         .symbol_expr();
  code_declt array_decl(new_array_data_symbol);
  array_decl.add_source_location() = location;
  dest.insert_before(next, goto_programt::make_decl(array_decl, location));
  dest.insert_before(
    next,
    goto_programt::make_assignment(
      code_assignt(new_array_data_symbol, data_java_new_expr), location));

  exprt cast_java_new = new_array_data_symbol;
  if(cast_java_new.type() != data.type())
    cast_java_new = typecast_exprt(cast_java_new, data.type());
  dest.insert_before(
    next,
    goto_programt::make_assignment(
      code_assignt(data, cast_java_new), location));

  // zero-initialize the data
  if(!rhs.get_bool(ID_skip_initialize))
  {
    const auto zero_element =
      zero_initializer(data.type().subtype(), location, ns);
    CHECK_RETURN(zero_element.has_value());
    codet array_set(ID_array_set);
    array_set.copy_to_operands(new_array_data_symbol, *zero_element);
    dest.insert_before(next, goto_programt::make_other(array_set, location));
  }

  // multi-dimensional?

  if(rhs.operands().size() >= 2)
  {
    // produce
    // for(int i=0; i<size; i++) tmp[i]=java_new(dim-1);
    // This will be converted recursively.

    goto_programt tmp;

    symbol_exprt tmp_i =
      fresh_java_symbol(
        length.type(), "tmp_index", location, function_identifier, symbol_table)
        .symbol_expr();
    code_declt decl(tmp_i);
    decl.add_source_location() = location;
    tmp.insert_before(
      tmp.instructions.begin(), goto_programt::make_decl(decl, location));

    side_effect_exprt sub_java_new = rhs;
    sub_java_new.operands().erase(sub_java_new.operands().begin());

    // we already know that rhs has pointer type
    typet sub_type =
      static_cast<const typet &>(rhs.type().subtype().find(ID_element_type));
    CHECK_RETURN(sub_type.id() == ID_pointer);
    sub_java_new.type() = sub_type;

    plus_exprt(tmp_i, from_integer(1, tmp_i.type()));
    dereference_exprt deref_expr(
      plus_exprt(data, tmp_i), data.type().subtype());

    code_blockt for_body;
    symbol_exprt init_sym =
      fresh_java_symbol(
        sub_type, "subarray_init", location, function_identifier, symbol_table)
        .symbol_expr();
    code_declt init_decl(init_sym);
    init_decl.add_source_location() = location;
    for_body.add(std::move(init_decl));

    code_assignt init_subarray(init_sym, sub_java_new);
    for_body.add(std::move(init_subarray));
    code_assignt assign_subarray(
      deref_expr, typecast_exprt(init_sym, deref_expr.type()));
    for_body.add(std::move(assign_subarray));

    const code_fort for_loop = code_fort::from_index_bounds(
      from_integer(0, tmp_i.type()),
      to_multi_ary_expr(rhs).op0(),
      tmp_i,
      std::move(for_body),
      location);

    goto_convert(for_loop, symbol_table, tmp, message_handler, ID_java);

    // lower new side effects recursively
    lower_java_new(function_identifier, tmp, message_handler);

    dest.destructive_insert(next, tmp);
  }

  return std::prev(next);
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \param function_identifier: Name of the function containing \p target.
/// \param goto_program: program to process
/// \param target: instruction to check for java_new expressions
/// \param message_handler: message handler
/// \return true if a replacement has been made
goto_programt::targett remove_java_newt::lower_java_new(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  goto_programt::targett target,
  message_handlert &message_handler)
{
  if(!target->is_assign())
    return target;

  if(as_const(*target).assign_rhs().id() == ID_side_effect)
  {
    // we make a copy, as we intend to destroy the assignment
    // inside lower_java_new and lower_java_new_array
    exprt lhs = target->assign_lhs();
    exprt rhs = target->assign_rhs();

    const auto &side_effect_expr = to_side_effect_expr(rhs);
    const auto &statement = side_effect_expr.get_statement();

    if(statement == ID_java_new)
    {
      return lower_java_new(
        function_identifier, lhs, side_effect_expr, goto_program, target);
    }
    else if(statement == ID_java_new_array)
    {
      return lower_java_new_array(
        function_identifier,
        lhs,
        side_effect_expr,
        goto_program,
        target,
        message_handler);
    }
  }

  return target;
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param function_identifier: Name of the function \p goto_program.
/// \param goto_program: The function body to work on.
/// \param message_handler: message handler
/// \return true if one or more java_new expressions have been replaced
bool remove_java_newt::lower_java_new(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  message_handlert &message_handler)
{
  bool changed = false;
  for(goto_programt::instructionst::iterator target =
        goto_program.instructions.begin();
      target != goto_program.instructions.end();
      ++target)
  {
    goto_programt::targett new_target = lower_java_new(
      function_identifier, goto_program, target, message_handler);
    changed = changed || new_target == target;
    target = new_target;
  }
  if(!changed)
    return false;
  goto_program.update();
  return true;
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param function_identifier: Name of the function containing \p target.
/// \param target: The instruction to work on.
/// \param goto_program: The function body containing the instruction.
/// \param symbol_table: The symbol table to add symbols to.
/// \param message_handler: a message handler
void remove_java_new(
  const irep_idt &function_identifier,
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  remove_java_newt rem{symbol_table};
  rem.lower_java_new(
    function_identifier, goto_program, target, message_handler);
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param function_identifier: Name of the function \p function.
/// \param function: The function to work on.
/// \param symbol_table: The symbol table to add symbols to.
/// \param message_handler: a message handler
void remove_java_new(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  remove_java_newt rem{symbol_table};
  rem.lower_java_new(function_identifier, function.body, message_handler);
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_functions: The functions to work on.
/// \param symbol_table: The symbol table to add symbols to.
/// \param message_handler: a message handler
void remove_java_new(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  remove_java_newt rem{symbol_table};
  bool changed = false;
  for(auto &f : goto_functions.function_map)
    changed =
      rem.lower_java_new(f.first, f.second.body, message_handler) || changed;
  if(changed)
    goto_functions.compute_location_numbers();
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_model: The functions to work on and the symbol table to add
///   symbols to.
/// \param message_handler: a message handler
void remove_java_new(goto_modelt &goto_model, message_handlert &message_handler)
{
  remove_java_new(
    goto_model.goto_functions, goto_model.symbol_table, message_handler);
}
