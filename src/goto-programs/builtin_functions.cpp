/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/rational.h>
#include <util/rational_tools.h>

#include <langapi/language_util.h>

#include "format_strings.h"
#include "class_identifier.h"

void goto_convertt::do_prob_uniform(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &identifier = function.get_identifier();

  // make it a side effect if there is an LHS
  if(arguments.size()!=2)
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier
            << "' expected to have two arguments" << eom;
    throw 0;
  }

  if(lhs.is_nil())
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier << "' expected to have LHS" << eom;
    throw 0;
  }

  auto rhs =
    side_effect_exprt("prob_uniform", lhs.type(), function.source_location());

  if(lhs.type().id()!=ID_unsignedbv &&
     lhs.type().id()!=ID_signedbv)
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier << "' expected other type" << eom;
    throw 0;
  }

  if(arguments[0].type().id()!=lhs.type().id() ||
     arguments[1].type().id()!=lhs.type().id())
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier
            << "' expected operands to be of same type as LHS" << eom;
    throw 0;
  }

  if(!arguments[0].is_constant() ||
     !arguments[1].is_constant())
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier
            << "' expected operands to be constant literals" << eom;
    throw 0;
  }

  mp_integer lb, ub;

  if(to_integer(arguments[0], lb) ||
     to_integer(arguments[1], ub))
  {
    error().source_location=function.find_source_location();
    error() << "error converting operands" << eom;
    throw 0;
  }

  if(lb > ub)
  {
    error().source_location=function.find_source_location();
    error() << "expected lower bound to be smaller or equal to the "
            << "upper bound" << eom;
    throw 0;
  }

  rhs.copy_to_operands(arguments[0], arguments[1]);

  code_assignt assignment(lhs, rhs);
  assignment.add_source_location()=function.source_location();
  copy(assignment, ASSIGN, dest);
}

void goto_convertt::do_prob_coin(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &identifier = function.get_identifier();

  // make it a side effect if there is an LHS
  if(arguments.size()!=2)
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier << "' expected to have two arguments"
            << eom;
    throw 0;
  }

  if(lhs.is_nil())
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier << "' expected to have LHS" << eom;
    throw 0;
  }

  side_effect_exprt rhs("prob_coin", lhs.type(), function.source_location());

  if(lhs.type()!=bool_typet())
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier << "' expected bool" << eom;
    throw 0;
  }

  if(arguments[0].type().id()!=ID_unsignedbv ||
     arguments[0].id()!=ID_constant)
  {
    error().source_location=function.find_source_location();
    error() << "`" << identifier << "' expected first operand to be "
            << "a constant literal of type unsigned long" << eom;
    throw 0;
  }

  mp_integer num, den;

  if(to_integer(arguments[0], num) ||
     to_integer(arguments[1], den))
  {
    error().source_location=function.find_source_location();
    error() << "error converting operands" << eom;
    throw 0;
  }

  if(num-den > mp_integer(0))
  {
    error().source_location=function.find_source_location();
    error() << "probability has to be smaller than 1" << eom;
    throw 0;
  }

  if(den == mp_integer(0))
  {
    error().source_location=function.find_source_location();
    error() << "denominator may not be zero" << eom;
    throw 0;
  }

  rationalt numerator(num), denominator(den);
  rationalt prob = numerator / denominator;

  rhs.copy_to_operands(from_rational(prob));

  code_assignt assignment(lhs, rhs);
  assignment.add_source_location()=function.source_location();
  copy(assignment, ASSIGN, dest);
}

void goto_convertt::do_printf(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &f_id = function.get_identifier();

  if(f_id==CPROVER_PREFIX "printf" ||
     f_id=="printf")
  {
    const typet &return_type = to_code_type(function.type()).return_type();
    side_effect_exprt printf_code(
      ID_printf, return_type, function.source_location());

    printf_code.operands()=arguments;
    printf_code.add_source_location()=function.source_location();

    if(lhs.is_not_nil())
    {
      code_assignt assignment(lhs, printf_code);
      assignment.add_source_location()=function.source_location();
      copy(assignment, ASSIGN, dest);
    }
    else
    {
      printf_code.id(ID_code);
      printf_code.type()=typet(ID_code);
      copy(to_code(printf_code), OTHER, dest);
    }
  }
  else
    UNREACHABLE;
}

void goto_convertt::do_scanf(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &f_id = function.get_identifier();

  if(f_id==CPROVER_PREFIX "scanf")
  {
    if(arguments.empty())
    {
      error().source_location=function.find_source_location();
      error() << "scanf takes at least one argument" << eom;
      throw 0;
    }

    irep_idt format_string;

    if(!get_string_constant(arguments[0], format_string))
    {
      // use our model
      format_token_listt token_list=
        parse_format_string(id2string(format_string));

      std::size_t argument_number=1;

      for(const auto &t : token_list)
      {
        typet type=get_type(t);

        if(type.is_not_nil())
        {
          if(argument_number<arguments.size())
          {
            const typecast_exprt ptr(
              arguments[argument_number], pointer_type(type));
            argument_number++;

            if(type.id()==ID_array)
            {
              #if 0
              // A string. We first need a nondeterministic size.
              exprt size=side_effect_expr_nondett(size_type());
              to_array_type(type).size()=size;

              const symbolt &tmp_symbol=
                new_tmp_symbol(
                  type, "scanf_string", dest, function.source_location());

              const address_of_exprt rhs(
                index_exprt(
                  tmp_symbol.symbol_expr(),
                  from_integer(0, index_type())));

              // now use array copy
              codet array_copy_statement;
              array_copy_statement.set_statement(ID_array_copy);
              array_copy_statement.operands().resize(2);
              array_copy_statement.op0()=ptr;
\              array_copy_statement.op1()=rhs;
              array_copy_statement.add_source_location()=
                function.source_location();

              copy(array_copy_statement, OTHER, dest);
              #else
              const index_exprt new_lhs(
                dereference_exprt(ptr, type), from_integer(0, index_type()));
              const side_effect_expr_nondett rhs(
                type.subtype(), function.source_location());
              code_assignt assign(new_lhs, rhs);
              assign.add_source_location()=function.source_location();
              copy(assign, ASSIGN, dest);
              #endif
            }
            else
            {
              // make it nondet for now
              const dereference_exprt new_lhs(ptr, type);
              const side_effect_expr_nondett rhs(
                type, function.source_location());
              code_assignt assign(new_lhs, rhs);
              assign.add_source_location()=function.source_location();
              copy(assign, ASSIGN, dest);
            }
          }
        }
      }
    }
    else
    {
      // we'll just do nothing
      code_function_callt function_call(lhs, function, arguments);
      function_call.add_source_location()=function.source_location();

      copy(function_call, FUNCTION_CALL, dest);
    }
  }
  else
    UNREACHABLE;
}

void goto_convertt::do_input(
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet input_code(ID_input);
  input_code.operands()=arguments;
  input_code.add_source_location()=function.source_location();

  if(arguments.size()<2)
  {
    error().source_location=function.find_source_location();
    error() << "input takes at least two arguments" << eom;
    throw 0;
  }

  copy(input_code, OTHER, dest);
}

void goto_convertt::do_output(
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet output_code(ID_output);
  output_code.operands()=arguments;
  output_code.add_source_location()=function.source_location();

  if(arguments.size()<2)
  {
    error().source_location=function.find_source_location();
    error() << "output takes at least two arguments" << eom;
    throw 0;
  }

  copy(output_code, OTHER, dest);
}

void goto_convertt::do_atomic_begin(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(lhs.is_not_nil())
  {
    error().source_location=lhs.find_source_location();
    error() << "atomic_begin does not expect an LHS" << eom;
    throw 0;
  }

  if(!arguments.empty())
  {
    error().source_location=function.find_source_location();
    error() << "atomic_begin takes no arguments" << eom;
    throw 0;
  }

  goto_programt::targett t=dest.add_instruction(ATOMIC_BEGIN);
  t->source_location=function.source_location();
}

void goto_convertt::do_atomic_end(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(lhs.is_not_nil())
  {
    error().source_location=lhs.find_source_location();
    error() << "atomic_end does not expect an LHS" << eom;
    throw 0;
  }

  if(!arguments.empty())
  {
    error().source_location=function.find_source_location();
    error() << "atomic_end takes no arguments" << eom;
    throw 0;
  }

  goto_programt::targett t=dest.add_instruction(ATOMIC_END);
  t->source_location=function.source_location();
}

void goto_convertt::do_cpp_new(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  if(lhs.is_nil())
  {
    error().source_location=lhs.find_source_location();
    error() << "do_cpp_new without lhs is yet to be implemented" << eom;
    throw 0;
  }

  // build size expression
  exprt object_size=
    static_cast<const exprt &>(rhs.find(ID_sizeof));

  bool new_array=rhs.get(ID_statement)==ID_cpp_new_array;

  exprt count;

  if(new_array)
  {
    count=static_cast<const exprt &>(rhs.find(ID_size));

    if(count.type()!=object_size.type())
      count.make_typecast(object_size.type());

    // might have side-effect
    clean_expr(count, dest, ID_cpp);
  }

  exprt tmp_symbol_expr;

  // is this a placement new?
  if(rhs.operands().empty()) // no, "regular" one
  {
    // call __new or __new_array
    exprt new_symbol=
      ns.lookup(new_array?"__new_array":"__new").symbol_expr();

    const code_typet &code_type=
      to_code_type(new_symbol.type());

    const typet &return_type=
      code_type.return_type();

    assert(code_type.parameters().size()==1 ||
           code_type.parameters().size()==2);

    const symbolt &tmp_symbol =
      new_tmp_symbol(return_type, "new", dest, rhs.source_location(), ID_cpp);

    tmp_symbol_expr=tmp_symbol.symbol_expr();

    code_function_callt new_call(new_symbol);
    if(new_array)
      new_call.arguments().push_back(count);
    new_call.arguments().push_back(object_size);
    new_call.set(ID_C_cxx_alloc_type, lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.add_source_location()=rhs.source_location();

    convert(new_call, dest, ID_cpp);
  }
  else if(rhs.operands().size()==1)
  {
    // call __placement_new
    exprt new_symbol=
      ns.lookup(
        new_array?"__placement_new_array":"__placement_new").symbol_expr();

    const code_typet &code_type=
      to_code_type(new_symbol.type());

    const typet &return_type=code_type.return_type();

    assert(code_type.parameters().size()==2 ||
           code_type.parameters().size()==3);

    const symbolt &tmp_symbol =
      new_tmp_symbol(return_type, "new", dest, rhs.source_location(), ID_cpp);

    tmp_symbol_expr=tmp_symbol.symbol_expr();

    code_function_callt new_call(new_symbol);
    if(new_array)
      new_call.arguments().push_back(count);
    new_call.arguments().push_back(object_size);
    new_call.arguments().push_back(rhs.op0()); // memory location
    new_call.set(ID_C_cxx_alloc_type, lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.add_source_location()=rhs.source_location();

    for(std::size_t i=0; i<code_type.parameters().size(); i++)
      if(new_call.arguments()[i].type()!=code_type.parameters()[i].type())
        new_call.arguments()[i].make_typecast(code_type.parameters()[i].type());

    convert(new_call, dest, ID_cpp);
  }
  else
  {
    error().source_location=rhs.find_source_location();
    error() << "cpp_new expected to have 0 or 1 operands" << eom;
    throw 0;
  }

  goto_programt::targett t_n=dest.add_instruction(ASSIGN);
  t_n->code=code_assignt(
    lhs, typecast_exprt(tmp_symbol_expr, lhs.type()));
  t_n->source_location=rhs.find_source_location();

  // grab initializer
  goto_programt tmp_initializer;
  cpp_new_initializer(lhs, rhs, tmp_initializer);

  dest.destructive_append(tmp_initializer);
}

/// builds a goto program for object initialization after new
void goto_convertt::cpp_new_initializer(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  exprt initializer=
    static_cast<const exprt &>(rhs.find(ID_initializer));

  if(initializer.is_not_nil())
  {
    if(rhs.get_statement()=="cpp_new[]")
    {
      // build loop
    }
    else if(rhs.get_statement()==ID_cpp_new)
    {
      // just one object
      const dereference_exprt deref_lhs(lhs, rhs.type().subtype());

      replace_new_object(deref_lhs, initializer);
      convert(to_code(initializer), dest, ID_cpp);
    }
    else
      UNREACHABLE;
  }
}

exprt goto_convertt::get_array_argument(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    assert(src.operands().size()==1);
    return get_array_argument(src.op0());
  }

  if(src.id()!=ID_address_of)
  {
    error().source_location=src.find_source_location();
    error() << "expected array-pointer as argument" << eom;
    throw 0;
  }

  assert(src.operands().size()==1);

  if(src.op0().id()!=ID_index)
  {
    error().source_location=src.find_source_location();
    error() << "expected array-element as argument" << eom;
    throw 0;
  }

  assert(src.op0().operands().size()==2);

  if(src.op0().op0().type().id() != ID_array)
  {
    error().source_location=src.find_source_location();
    error() << "expected array as argument" << eom;
    throw 0;
  }

  return src.op0().op0();
}

void goto_convertt::do_array_op(
  const irep_idt &id,
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    error().source_location=function.find_source_location();
    error() << id << " expects two arguments" << eom;
    throw 0;
  }

  codet array_op_statement(id);
  array_op_statement.operands()=arguments;
  array_op_statement.add_source_location()=function.source_location();

  // lhs is only used with array_equal, in all other cases it should be nil (as
  // they are of type void)
  if(id == ID_array_equal)
    array_op_statement.copy_to_operands(lhs);

  copy(array_op_statement, OTHER, dest);
}

exprt make_va_list(const exprt &expr)
{
  // we first strip any typecast
  if(expr.id()==ID_typecast)
    return make_va_list(to_typecast_expr(expr).op());

  // if it's an address of an lvalue, we take that
  if(expr.id()==ID_address_of &&
     expr.operands().size()==1 &&
     is_lvalue(expr.op0()))
    return expr.op0();

  return expr;
}

/// add function calls to function queue for later processing
void goto_convertt::do_function_call_symbol(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(function.get_bool(ID_C_invalid_object))
    return; // ignore

  // lookup symbol
  const irep_idt &identifier=function.get_identifier();

  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
  {
    error().source_location=function.find_source_location();
    error() << "error: function `" << identifier << "' not found"
            << eom;
    throw 0;
  }

  if(symbol->type.id()!=ID_code)
  {
    error().source_location=function.find_source_location();
    error() << "error: function `" << identifier
            << "' type mismatch: expected code" << eom;
    throw 0;
  }

  if(identifier==CPROVER_PREFIX "assume" ||
     identifier=="__VERIFIER_assume")
  {
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have one argument"
              << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(ASSUME);
    t->guard=arguments.front();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);

    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }
  }
  else if(identifier=="__VERIFIER_error")
  {
    if(!arguments.empty())
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have no arguments"
              << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }

    // __VERIFIER_error has abort() semantics, even if no assertions
    // are being checked
    goto_programt::targett a=dest.add_instruction(ASSUME);
    a->guard=false_exprt();
    a->source_location=function.source_location();
    a->source_location.set("user-provided", true);
  }
  else if(identifier=="assert" &&
          !ns.lookup(identifier).location.get_function().empty())
  {
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have one argument"
              << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=arguments.front();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(
      "assertion " + id2string(from_expr(ns, identifier, t->guard)));

    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }
  }
  else if(identifier==CPROVER_PREFIX "assert" ||
          identifier==CPROVER_PREFIX "precondition")
  {
    if(arguments.size()!=2)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have two arguments"
              << eom;
      throw 0;
    }

    bool is_precondition=
      identifier==CPROVER_PREFIX "precondition";

    const irep_idt description=
      get_string_constant(arguments[1]);

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=arguments[0];
    t->source_location=function.source_location();

    if(is_precondition)
    {
      t->source_location.set_property_class(ID_precondition);
    }
    else
    {
      t->source_location.set(
        "user-provided",
        !function.source_location().is_built_in());
      t->source_location.set_property_class(ID_assertion);
    }

    t->source_location.set_comment(description);

    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }
  }
  else if(identifier==CPROVER_PREFIX "havoc_object")
  {
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have one argument"
              << eom;
      throw 0;
    }

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(OTHER);
    t->source_location=function.source_location();
    t->code=codet(ID_havoc_object);
    t->code.add_source_location()=function.source_location();
    t->code.copy_to_operands(arguments[0]);
  }
  else if(identifier==CPROVER_PREFIX "printf")
  {
    do_printf(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "scanf")
  {
    do_scanf(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "input" ||
          identifier=="__CPROVER::input")
  {
    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }

    do_input(function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "output" ||
          identifier=="__CPROVER::output")
  {
    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }

    do_output(function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_begin" ||
          identifier=="__CPROVER::atomic_begin" ||
          identifier=="java::org.cprover.CProver.atomicBegin:()V" ||
          identifier=="__VERIFIER_atomic_begin")
  {
    do_atomic_begin(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_end" ||
          identifier=="__CPROVER::atomic_end" ||
          identifier=="java::org.cprover.CProver.atomicEnd:()V" ||
          identifier=="__VERIFIER_atomic_end")
  {
    do_atomic_end(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "prob_biased_coin")
  {
    do_prob_coin(lhs, function, arguments, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "prob_uniform_"))
  {
    do_prob_uniform(lhs, function, arguments, dest);
  }
  else if(has_prefix(id2string(identifier), "nondet_") ||
          has_prefix(id2string(identifier), "__VERIFIER_nondet_"))
  {
    // make it a side effect if there is an LHS
    if(lhs.is_nil())
      return;

    exprt rhs;

    // We need to special-case for _Bool, which
    // can only be 0 or 1.
    if(lhs.type().id()==ID_c_bool)
    {
      rhs = side_effect_expr_nondett(bool_typet(), function.source_location());
      rhs.set(ID_C_identifier, identifier);
      rhs=typecast_exprt(rhs, lhs.type());
    }
    else
    {
      rhs = side_effect_expr_nondett(lhs.type(), function.source_location());
      rhs.set(ID_C_identifier, identifier);
    }

    code_assignt assignment(lhs, rhs);
    assignment.add_source_location()=function.source_location();
    copy(assignment, ASSIGN, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "uninterpreted_"))
  {
    // make it a side effect if there is an LHS
    if(lhs.is_nil())
      return;

    const function_application_exprt rhs(function, arguments, lhs.type());

    code_assignt assignment(lhs, rhs);
    assignment.add_source_location()=function.source_location();
    copy(assignment, ASSIGN, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_equal")
  {
    do_array_op(ID_array_equal, lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_set")
  {
    do_array_op(ID_array_set, lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_copy")
  {
    do_array_op(ID_array_copy, lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_replace")
  {
    do_array_op(ID_array_replace, lhs, function, arguments, dest);
  }
  else if(identifier=="printf")
  /*
          identifier=="fprintf" ||
          identifier=="sprintf" ||
          identifier=="snprintf")
  */
  {
    do_printf(lhs, function, arguments, dest);
  }
  else if(identifier=="__assert_fail" ||
          identifier=="_assert" ||
          identifier=="__assert_c99" ||
          identifier=="_wassert")
  {
    // __assert_fail is Linux
    // These take four arguments:
    // "expression", "file.c", line, __func__
    // klibc has __assert_fail with 3 arguments
    // "expression", "file.c", line

    // MingW has
    // void _assert (const char*, const char*, int);
    // with three arguments:
    // "expression", "file.c", line

    // This has been seen in Solaris 11.
    // Signature:
    // void __assert_c99(
    //   const char *desc, const char *file, int line, const char *func);

    // _wassert is Windows. The arguments are
    // L"expression", L"file.c", line

    if(arguments.size()!=4 &&
       arguments.size()!=3)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have four arguments"
              << eom;
      throw 0;
    }

    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="__assert_rtn" ||
          identifier=="__assert")
  {
    // __assert_rtn has been seen on MacOS;
    // __assert is FreeBSD and Solaris 11.
    // These take four arguments:
    // __func__, "file.c", line, "expression"
    // On Solaris 11, it's three arguments:
    // "expression", "file", line

    irep_idt description;

    if(arguments.size()==4)
    {
      description=
        "assertion "+id2string(get_string_constant(arguments[3]));
    }
    else if(arguments.size()==3)
    {
      description=
        "assertion "+id2string(get_string_constant(arguments[1]));
    }
    else
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have four arguments"
              << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="__assert_func")
  {
    // __assert_func is newlib (used by, e.g., cygwin)
    // These take four arguments:
    // "file.c", line, __func__, "expression"
    if(arguments.size()!=4)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have four arguments"
              << eom;
      throw 0;
    }

    irep_idt description;
    try
    {
      description="assertion "+id2string(get_string_constant(arguments[3]));
    }
    catch(int)
    {
      // we might be building newlib, where __assert_func is passed
      // a pointer-typed symbol; the warning will still have been
      // printed
      description="assertion";
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier==CPROVER_PREFIX "fence")
  {
    if(arguments.empty())
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have at least one argument" << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(OTHER);
    t->source_location=function.source_location();
    t->code.set(ID_statement, ID_fence);

    forall_expr(it, arguments)
    {
      const irep_idt kind=get_string_constant(*it);
      t->code.set(kind, true);
    }
  }
  else if(identifier=="__builtin_prefetch")
  {
    // does nothing
  }
  else if(identifier=="__builtin_unreachable")
  {
    // says something like UNREACHABLE;
  }
  else if(identifier==ID_gcc_builtin_va_arg)
  {
    // This does two things.
    // 1) Move list pointer to next argument.
    //    Done by gcc_builtin_va_arg_next.
    // 2) Return value of argument.
    //    This is just dereferencing.

    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have one argument"
              << eom;
      throw 0;
    }

    exprt list_arg=make_va_list(arguments[0]);

    {
      side_effect_exprt rhs(
        ID_gcc_builtin_va_arg_next,
        list_arg.type(),
        function.source_location());
      rhs.copy_to_operands(list_arg);
      rhs.set(ID_C_va_arg_type, to_code_type(function.type()).return_type());
      goto_programt::targett t1=dest.add_instruction(ASSIGN);
      t1->source_location=function.source_location();
      t1->code=code_assignt(list_arg, rhs);
    }

    if(lhs.is_not_nil())
    {
      typet t=pointer_type(lhs.type());
      dereference_exprt rhs(lhs.type());
      rhs.op0()=typecast_exprt(list_arg, t);
      rhs.add_source_location()=function.source_location();
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, rhs);
    }
  }
  else if(identifier=="__builtin_va_copy")
  {
    if(arguments.size()!=2)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have two arguments"
              << eom;
      throw 0;
    }

    exprt dest_expr=make_va_list(arguments[0]);
    const typecast_exprt src_expr(arguments[1], dest_expr.type());

    if(!is_lvalue(dest_expr))
    {
      error().source_location=dest_expr.find_source_location();
      error() << "va_copy argument expected to be lvalue" << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->source_location=function.source_location();
    t->code=code_assignt(dest_expr, src_expr);
  }
  else if(identifier=="__builtin_va_start")
  {
    // Set the list argument to be the address of the
    // parameter argument.
    if(arguments.size()!=2)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have two arguments"
              << eom;
      throw 0;
    }

    exprt dest_expr=make_va_list(arguments[0]);
    const typecast_exprt src_expr(
      address_of_exprt(arguments[1]), dest_expr.type());

    if(!is_lvalue(dest_expr))
    {
      error().source_location=dest_expr.find_source_location();
      error() << "va_start argument expected to be lvalue" << eom;
      throw 0;
    }

    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->source_location=function.source_location();
    t->code=code_assignt(dest_expr, src_expr);
  }
  else if(identifier=="__builtin_va_end")
  {
    // Invalidates the argument. We do so by setting it to NULL.
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have one argument"
              << eom;
      throw 0;
    }

    exprt dest_expr=make_va_list(arguments[0]);

    if(!is_lvalue(dest_expr))
    {
      error().source_location=dest_expr.find_source_location();
      error() << "va_end argument expected to be lvalue" << eom;
      throw 0;
    }

    // our __builtin_va_list is a pointer
    if(dest_expr.type().id() == ID_pointer)
    {
      goto_programt::targett t=dest.add_instruction(ASSIGN);
      t->source_location=function.source_location();
      const auto zero =
        zero_initializer(dest_expr.type(), function.source_location(), ns);
      CHECK_RETURN(zero.has_value());
      t->code = code_assignt(dest_expr, *zero);
    }
  }
  else if(identifier=="__sync_fetch_and_add" ||
          identifier=="__sync_fetch_and_sub" ||
          identifier=="__sync_fetch_and_or" ||
          identifier=="__sync_fetch_and_and" ||
          identifier=="__sync_fetch_and_xor" ||
          identifier=="__sync_fetch_and_nand")
  {
    // type __sync_fetch_and_OP(type *ptr, type value, ...)
    // { tmp = *ptr; *ptr OP= value; return tmp; }

    if(arguments.size()<2)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have at least two arguments" << eom;
      throw 0;
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier << "' expected to have pointer argument"
              << eom;
      throw 0;
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }

    irep_idt op_id=
      identifier=="__sync_fetch_and_add"?ID_plus:
      identifier=="__sync_fetch_and_sub"?ID_minus:
      identifier=="__sync_fetch_and_or"?ID_bitor:
      identifier=="__sync_fetch_and_and"?ID_bitand:
      identifier=="__sync_fetch_and_xor"?ID_bitxor:
      identifier=="__sync_fetch_and_nand"?ID_bitnand:
      ID_nil;

    // build *ptr=*ptr OP arguments[1];
    binary_exprt op_expr(deref_ptr, op_id, arguments[1], deref_ptr.type());
    if(op_expr.op1().type()!=op_expr.type())
      op_expr.op1().make_typecast(op_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, op_expr);

    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);

    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_add_and_fetch" ||
          identifier=="__sync_sub_and_fetch" ||
          identifier=="__sync_or_and_fetch" ||
          identifier=="__sync_and_and_fetch" ||
          identifier=="__sync_xor_and_fetch" ||
          identifier=="__sync_nand_and_fetch")
  {
    // type __sync_OP_and_fetch (type *ptr, type value, ...)
    // { *ptr OP= value; return *ptr; }

    if(arguments.size()<2)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have at least two arguments" << eom;
      throw 0;
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have pointer argument" << eom;
      throw 0;
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    irep_idt op_id=
      identifier=="__sync_add_and_fetch"?ID_plus:
      identifier=="__sync_sub_and_fetch"?ID_minus:
      identifier=="__sync_or_and_fetch"?ID_bitor:
      identifier=="__sync_and_and_fetch"?ID_bitand:
      identifier=="__sync_xor_and_fetch"?ID_bitxor:
      identifier=="__sync_nand_and_fetch"?ID_bitnand:
      ID_nil;

    // build *ptr=*ptr OP arguments[1];
    binary_exprt op_expr(deref_ptr, op_id, arguments[1], deref_ptr.type());
    if(op_expr.op1().type()!=op_expr.type())
      op_expr.op1().make_typecast(op_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, op_expr);

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }

    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);

    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_bool_compare_and_swap")
  {
    // These builtins perform an atomic compare and swap. That is, if the
    // current value of *ptr is oldval, then write newval into *ptr.  The
    // "bool" version returns true if the comparison is successful and
    // newval was written.  The "val" version returns the contents of *ptr
    // before the operation.

    // These are type-polymorphic, which makes it hard to put
    // them into ansi-c/library.

    // bool __sync_bool_compare_and_swap(
    //   type *ptr, type oldval, type newval, ...)

    if(arguments.size()<3)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have at least three arguments" << eom;
      throw 0;
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have pointer argument" << eom;
      throw 0;
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    // build *ptr==oldval
    equal_exprt equal(deref_ptr, arguments[1]);
    if(equal.op1().type()!=equal.op0().type())
      equal.op1().make_typecast(equal.op0().type());

    if(lhs.is_not_nil())
    {
      // return *ptr==oldval
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, equal);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }

    // build (*ptr==oldval)?newval:*ptr
    if_exprt if_expr(equal, arguments[2], deref_ptr, deref_ptr.type());
    if(if_expr.op1().type()!=if_expr.type())
      if_expr.op1().make_typecast(if_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, if_expr);

    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);

    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_val_compare_and_swap")
  {
    // type __sync_val_compare_and_swap(
    //   type *ptr, type oldval, type newval, ...)
    if(arguments.size()<3)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have at least three arguments" << eom;
      throw 0;
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have pointer argument" << eom;
      throw 0;
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }

    // build *ptr==oldval
    equal_exprt equal(deref_ptr, arguments[1]);
    if(equal.op1().type()!=equal.op0().type())
      equal.op1().make_typecast(equal.op0().type());

    // build (*ptr==oldval)?newval:*ptr
    if_exprt if_expr(equal, arguments[2], deref_ptr, deref_ptr.type());
    if(if_expr.op1().type()!=if_expr.type())
      if_expr.op1().make_typecast(if_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, if_expr);

    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);

    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_lock_test_and_set")
  {
    // type __sync_lock_test_and_set (type *ptr, type value, ...)

    // This builtin, as described by Intel, is not a traditional
    // test-and-set operation, but rather an atomic exchange operation.
    // It writes value into *ptr, and returns the previous contents of
    // *ptr.  Many targets have only minimal support for such locks, and
    // do not support a full exchange operation.  In this case, a target
    // may support reduced functionality here by which the only valid
    // value to store is the immediate constant 1.  The exact value
    // actually stored in *ptr is implementation defined.
  }
  else if(identifier=="__sync_lock_release")
  {
    // This builtin is not a full barrier, but rather an acquire barrier.
    // This means that references after the builtin cannot move to (or be
    // speculated to) before the builtin, but previous memory stores may
    // not be globally visible yet, and previous memory loads may not yet
    // be satisfied.

    // void __sync_lock_release (type *ptr, ...)
  }
  else if(identifier=="__builtin_isgreater" ||
          identifier=="__builtin_isgreater" ||
          identifier=="__builtin_isgreaterequal" ||
          identifier=="__builtin_isless" ||
          identifier=="__builtin_islessequal" ||
          identifier=="__builtin_islessgreater" ||
          identifier=="__builtin_isunordered")
  {
    // these support two double or two float arguments; we call the
    // appropriate internal version
    if(arguments.size()!=2 ||
       (arguments[0].type()!=double_type() &&
        arguments[0].type()!=float_type()) ||
       (arguments[1].type()!=double_type() &&
        arguments[1].type()!=float_type()))
    {
      error().source_location=function.find_source_location();
      error() << "`" << identifier
              << "' expected to have two float/double arguments"
              << eom;
      throw 0;
    }

    exprt::operandst new_arguments=arguments;

    bool use_double=arguments[0].type()==double_type();
    if(arguments[0].type()!=arguments[1].type())
    {
      if(use_double)
        new_arguments[1].make_typecast(arguments[0].type());
      else
      {
        new_arguments[0].make_typecast(arguments[1].type());
        use_double=true;
      }
    }

    code_typet f_type=to_code_type(function.type());
    f_type.remove_ellipsis();
    const typet &a_t=new_arguments[0].type();
    f_type.parameters()=
      code_typet::parameterst(2, code_typet::parametert(a_t));

    // replace __builtin_ by CPROVER_PREFIX
    std::string name=CPROVER_PREFIX+id2string(identifier).substr(10);
    // append d or f for double/float
    name+=use_double?'d':'f';

    symbol_exprt new_function=function;
    new_function.set_identifier(name);
    new_function.type()=f_type;

    code_function_callt function_call(lhs, new_function, new_arguments);
    function_call.add_source_location()=function.source_location();

    if(!symbol_table.has_symbol(name))
    {
      symbolt new_symbol;
      new_symbol.base_name=name;
      new_symbol.name=name;
      new_symbol.type=f_type;
      new_symbol.location=function.source_location();
      symbol_table.add(new_symbol);
    }

    copy(function_call, FUNCTION_CALL, dest);
  }
  else
  {
    do_function_call_symbol(*symbol);

    // insert function call
    code_function_callt function_call(lhs, function, arguments);
    function_call.add_source_location()=function.source_location();

    copy(function_call, FUNCTION_CALL, dest);
  }
}
