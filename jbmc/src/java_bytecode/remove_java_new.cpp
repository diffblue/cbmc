/*******************************************************************\

Module: Remove Java New Operators

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Remove Java New Operators

#include "remove_java_new.h"

#include <goto-programs/class_identifier.h>
#include <goto-programs/goto_convert.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_cast.h>
#include <util/expr_initializer.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>

class remove_java_newt : public messaget
{
public:
  remove_java_newt(
    symbol_table_baset &symbol_table,
    message_handlert &_message_handler)
    : messaget(_message_handler), symbol_table(symbol_table), ns(symbol_table)
  {
  }

  // Lower java_new for a single function
  bool lower_java_new(goto_programt &);

  // Lower java_new for a single instruction
  goto_programt::targett
  lower_java_new(goto_programt &, goto_programt::targett);

protected:
  symbol_table_baset &symbol_table;
  namespacet ns;

  goto_programt::targett lower_java_new(
    exprt lhs,
    side_effect_exprt rhs,
    goto_programt &,
    goto_programt::targett);

  goto_programt::targett lower_java_new_array(
    exprt lhs,
    side_effect_exprt rhs,
    goto_programt &,
    goto_programt::targett);
};

/// Replaces the instruction `lhs = new java_type` by
/// two instructions:
///   lhs = ALLOCATE(java_type)
///   *lhs = { zero-initialized java_type }
/// \param lhs: the lhs
/// \param rhs: the rhs
/// \param dest: the goto program to modify
/// \param target: the goto instruction to replace
/// \return the iterator advanced to the last of the inserted instructions
/// Note: we have to take a copy of `lhs` and `rhs` since they would suffer
///   destruction when replacing the instruction.
goto_programt::targett remove_java_newt::lower_java_new(
  exprt lhs,
  side_effect_exprt rhs,
  goto_programt &dest,
  goto_programt::targett target)
{
  PRECONDITION(!lhs.is_nil());
  PRECONDITION(rhs.operands().empty());
  PRECONDITION(rhs.type().id() == ID_pointer);
  source_locationt location = rhs.source_location();
  typet object_type = rhs.type().subtype();

  // build size expression
  exprt object_size = size_of_expr(object_type, ns);
  CHECK_RETURN(object_size.is_not_nil());

  // we produce a malloc side-effect, which stays
  side_effect_exprt malloc_expr(ID_allocate, rhs.type(), location);
  malloc_expr.copy_to_operands(object_size);
  // could use true and get rid of the code below
  malloc_expr.copy_to_operands(false_exprt());
  target->make_assignment(code_assignt(lhs, malloc_expr));
  target->source_location = location;

  // zero-initialize the object
  dereference_exprt deref(lhs, object_type);
  auto zero_object = zero_initializer(object_type, location, ns);
  CHECK_RETURN(zero_object.has_value());
  set_class_identifier(
    to_struct_expr(*zero_object), ns, to_symbol_type(object_type));
  goto_programt::targett t_i = dest.insert_after(target);
  t_i->make_assignment(code_assignt(deref, *zero_object));
  t_i->source_location = location;

  return t_i;
}

/// Replaces the instruction `lhs = new java_array_type` by
/// the following code:
///   lhs = ALLOCATE(java_type)
///   loops to initialize the elements (including multi-dimensional arrays)
/// \param lhs: the lhs
/// \param rhs: the rhs
/// \param dest: the goto program to modify
/// \param target: the goto instruction to replace
/// \return the iterator advanced to the last of the inserted instructions
/// Note: we have to take a copy of `lhs` and `rhs` since they would suffer
///   destruction when replacing the instruction.
goto_programt::targett remove_java_newt::lower_java_new_array(
  exprt lhs,
  side_effect_exprt rhs,
  goto_programt &dest,
  goto_programt::targett target)
{
  // lower_java_new_array without lhs not implemented
  PRECONDITION(!lhs.is_nil());
  PRECONDITION(rhs.operands().size() >= 1); // one per dimension
  PRECONDITION(rhs.type().id() == ID_pointer);

  source_locationt location = rhs.source_location();
  typet object_type = rhs.type().subtype();
  PRECONDITION(ns.follow(object_type).id() == ID_struct);

  // build size expression
  exprt object_size = size_of_expr(object_type, ns);
  CHECK_RETURN(!object_size.is_nil());

  // we produce a malloc side-effect, which stays
  side_effect_exprt malloc_expr(ID_allocate, rhs.type(), location);
  malloc_expr.copy_to_operands(object_size);
  // code use true and get rid of the code below
  malloc_expr.copy_to_operands(false_exprt());

  target->make_assignment(code_assignt(lhs, malloc_expr));
  target->source_location = location;
  goto_programt::targett next = std::next(target);

  const struct_typet &struct_type = to_struct_type(ns.follow(object_type));

  // Ideally we would have a check for `is_valid_java_array(struct_type)` but
  // `is_valid_java_array is part of the java_bytecode module and we cannot
  // introduce such dependencies. We do this simple check instead:
  PRECONDITION(struct_type.components().size() == 3);

  // Init base class:
  dereference_exprt deref(lhs, object_type);
  auto zero_object = zero_initializer(object_type, location, ns);
  CHECK_RETURN(zero_object.has_value());
  set_class_identifier(
    to_struct_expr(*zero_object), ns, to_symbol_type(object_type));
  goto_programt::targett t_i = dest.insert_before(next);
  t_i->make_assignment(code_assignt(deref, *zero_object));
  t_i->source_location = location;

  // if it's an array, we need to set the length field
  member_exprt length(
    deref,
    struct_type.components()[1].get_name(),
    struct_type.components()[1].type());
  goto_programt::targett t_s = dest.insert_before(next);
  t_s->make_assignment(code_assignt(length, rhs.op0()));
  t_s->source_location = location;

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
    data_java_new_expr.set(ID_size, rhs.op0());
  else
    data_java_new_expr.set(ID_size, size_bound);

  // Must directly assign the new array to a temporary
  // because goto-symex will notice `x=side_effect_exprt` but not
  // `x=typecast_exprt(side_effect_exprt(...))`
  symbol_exprt new_array_data_symbol = get_fresh_aux_symbol(
                                         data_java_new_expr.type(),
                                         id2string(target->function),
                                         "tmp_new_data_array",
                                         location,
                                         ID_java,
                                         symbol_table)
                                         .symbol_expr();
  code_declt array_decl(new_array_data_symbol);
  array_decl.add_source_location() = location;
  goto_programt::targett t_array_decl = dest.insert_before(next);
  t_array_decl->make_decl(array_decl);
  t_array_decl->source_location = location;
  goto_programt::targett t_p2 = dest.insert_before(next);
  t_p2->make_assignment(
    code_assignt(new_array_data_symbol, data_java_new_expr));
  t_p2->source_location = location;

  goto_programt::targett t_p = dest.insert_before(next);
  exprt cast_java_new = new_array_data_symbol;
  if(cast_java_new.type() != data.type())
    cast_java_new = typecast_exprt(cast_java_new, data.type());
  t_p->make_assignment(code_assignt(data, cast_java_new));
  t_p->source_location = location;

  // zero-initialize the data
  if(!rhs.get_bool(ID_skip_initialize))
  {
    const auto zero_element =
      zero_initializer(data.type().subtype(), location, ns);
    CHECK_RETURN(zero_element.has_value());
    codet array_set(ID_array_set);
    array_set.copy_to_operands(new_array_data_symbol, *zero_element);
    goto_programt::targett t_d = dest.insert_before(next);
    t_d->make_other(array_set);
    t_d->source_location = location;
  }

  // multi-dimensional?

  if(rhs.operands().size() >= 2)
  {
    // produce
    // for(int i=0; i<size; i++) tmp[i]=java_new(dim-1);
    // This will be converted recursively.

    goto_programt tmp;

    symbol_exprt tmp_i = get_fresh_aux_symbol(
                           length.type(),
                           id2string(target->function),
                           "tmp_index",
                           location,
                           ID_java,
                           symbol_table)
                           .symbol_expr();
    code_declt decl(tmp_i);
    decl.add_source_location() = location;
    goto_programt::targett t_decl = tmp.insert_before(tmp.instructions.begin());
    t_decl->make_decl(decl);
    t_decl->source_location = location;

    code_fort for_loop;

    side_effect_exprt sub_java_new = rhs;
    sub_java_new.operands().erase(sub_java_new.operands().begin());

    // we already know that rhs has pointer type
    typet sub_type =
      static_cast<const typet &>(rhs.type().subtype().find(ID_element_type));
    CHECK_RETURN(sub_type.id() == ID_pointer);
    sub_java_new.type() = sub_type;

    side_effect_exprt inc(ID_assign, typet(), location);
    inc.operands().resize(2);
    inc.op0() = tmp_i;
    inc.op1() = plus_exprt(tmp_i, from_integer(1, tmp_i.type()));

    dereference_exprt deref_expr(
      plus_exprt(data, tmp_i), data.type().subtype());

    code_blockt for_body;
    symbol_exprt init_sym = get_fresh_aux_symbol(
                              sub_type,
                              id2string(target->function),
                              "subarray_init",
                              location,
                              ID_java,
                              symbol_table)
                              .symbol_expr();
    code_declt init_decl(init_sym);
    init_decl.add_source_location() = location;
    for_body.add(std::move(init_decl));

    code_assignt init_subarray(init_sym, sub_java_new);
    for_body.add(std::move(init_subarray));
    code_assignt assign_subarray(
      deref_expr, typecast_exprt(init_sym, deref_expr.type()));
    for_body.add(std::move(assign_subarray));

    for_loop.init() = code_assignt(tmp_i, from_integer(0, tmp_i.type()));
    for_loop.cond() = binary_relation_exprt(tmp_i, ID_lt, rhs.op0());
    for_loop.iter() = inc;
    for_loop.body() = for_body;

    goto_convert(for_loop, symbol_table, tmp, get_message_handler(), ID_java);

    // lower new side effects recursively
    lower_java_new(tmp);

    dest.destructive_insert(next, tmp);
  }

  return std::prev(next);
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \param goto_program: program to process
/// \param target: instruction to check for java_new expressions
/// \return true if a replacement has been made
goto_programt::targett remove_java_newt::lower_java_new(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const auto maybe_code_assign =
    expr_try_dynamic_cast<code_assignt>(target->code);
  if(!maybe_code_assign)
    return target;

  const exprt &lhs = maybe_code_assign->lhs();
  const exprt &rhs = maybe_code_assign->rhs();

  if(rhs.id() == ID_side_effect && rhs.get(ID_statement) == ID_java_new)
  {
    return lower_java_new(lhs, to_side_effect_expr(rhs), goto_program, target);
  }

  if(rhs.id() == ID_side_effect && rhs.get(ID_statement) == ID_java_new_array)
  {
    return lower_java_new_array(
      lhs, to_side_effect_expr(rhs), goto_program, target);
  }

  return target;
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// Extra auxiliary variables may be introduced into symbol_table.
/// \param goto_program: The function body to work on.
/// \return true if one or more java_new expressions have been replaced
bool remove_java_newt::lower_java_new(goto_programt &goto_program)
{
  bool changed = false;
  for(goto_programt::instructionst::iterator target =
        goto_program.instructions.begin();
      target != goto_program.instructions.end();
      ++target)
  {
    goto_programt::targett new_target = lower_java_new(goto_program, target);
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
/// \param target: The instruction to work on.
/// \param goto_program: The function body containing the instruction.
/// \param symbol_table: The symbol table to add symbols to.
/// \param message_handler: a message handler
void remove_java_new(
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  remove_java_newt rem(symbol_table, message_handler);
  rem.lower_java_new(goto_program, target);
}

/// Replace every java_new or java_new_array by a malloc side-effect
/// and zero initialization.
/// \remarks Extra auxiliary variables may be introduced into symbol_table.
/// \param function: The function to work on.
/// \param symbol_table: The symbol table to add symbols to.
/// \param message_handler: a message handler
void remove_java_new(
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  remove_java_newt rem(symbol_table, message_handler);
  rem.lower_java_new(function.body);
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
  remove_java_newt rem(symbol_table, message_handler);
  bool changed = false;
  for(auto &f : goto_functions.function_map)
    changed = rem.lower_java_new(f.second.body) || changed;
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
