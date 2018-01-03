// Copyright 2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Function-level/module-level pass to remove java_new and replace with
/// malloc & zero-initialize

#include "remove_java_new.h"

#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <linking/zero_initializer.h>

#include "class_identifier.h"

static bool remove_java_new(
  goto_programt &goto_program,
  const namespacet &ns,
  message_handlert &message_handler)
{
  messaget msg(message_handler);

  bool changed=false;
  for(goto_programt::targett target=goto_program.instructions.begin();
    target!=goto_program.instructions.end();
    ++target)
  {
    code_assignt *assign=expr_try_dynamic_cast<code_assignt>(target->code);
    if(assign==nullptr)
      continue;
    side_effect_exprt *rhs=
      expr_try_dynamic_cast<side_effect_exprt>(assign->rhs());
    if(rhs==nullptr)
      continue;
    if(rhs->get_statement()!=ID_java_new)
      continue;
    INVARIANT(rhs->operands().empty(), "java_new does not have operands");
    INVARIANT(rhs->type().id()==ID_pointer, "java_new returns pointer");

    const exprt &lhs=assign->lhs();
    INVARIANT(
      !lhs.is_nil(), "remove_java_new without lhs is yet to be implemented");

    typet object_type=rhs->type().subtype();

    // build size expression
    exprt object_size=size_of_expr(object_type, ns);
    CHECK_RETURN(object_size.is_not_nil());

    changed=true;

    source_locationt location=rhs->source_location();

    // We produce a malloc side-effect
    side_effect_exprt malloc_expr(ID_allocate);
    malloc_expr.copy_to_operands(object_size);
    // could use true and get rid of the code below
    malloc_expr.copy_to_operands(false_exprt());
    malloc_expr.type()=rhs->type();
    *rhs=std::move(malloc_expr);

    // zero-initialize the object
    dereference_exprt deref(lhs, object_type);
    exprt zero_object=
      zero_initializer(object_type, location, ns, message_handler);
    set_class_identifier(
      expr_dynamic_cast<struct_exprt>(zero_object),
      ns,
      to_symbol_type(object_type));
    goto_programt::targett zi_assign=goto_program.insert_after(target);
    zi_assign->make_assignment();
    zi_assign->code=code_assignt(deref, zero_object);
    zi_assign->source_location=location;
  }
  if(!changed)
    return false;
  goto_program.update();
  return true;
}

bool remove_java_new(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  message_handlert &message_handler)
{
  return remove_java_new(goto_function.body, ns, message_handler);
}

void remove_java_new(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler)
{
  for(auto &named_fn : goto_functions.function_map)
    remove_java_new(named_fn.second, ns, message_handler);
}

void remove_java_new(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  remove_java_new(
    goto_model.goto_functions,
    namespacet(goto_model.symbol_table),
    message_handler);
}
