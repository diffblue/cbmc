/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/rational.h>
#include <util/rational_tools.h>
#include <util/symbol_table.h>

#include <langapi/language_util.h>

#include "format_strings.h"

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
    error() << "'" << identifier << "' expected to have two arguments" << eom;
    throw 0;
  }

  if(lhs.is_nil())
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier << "' expected to have LHS" << eom;
    throw 0;
  }

  auto rhs =
    side_effect_exprt("prob_uniform", lhs.type(), function.source_location());

  if(lhs.type().id()!=ID_unsignedbv &&
     lhs.type().id()!=ID_signedbv)
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier << "' expected other type" << eom;
    throw 0;
  }

  if(arguments[0].type().id()!=lhs.type().id() ||
     arguments[1].type().id()!=lhs.type().id())
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier
            << "' expected operands to be of same type as LHS" << eom;
    throw 0;
  }

  if(!arguments[0].is_constant() ||
     !arguments[1].is_constant())
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier
            << "' expected operands to be constant literals" << eom;
    throw 0;
  }

  mp_integer lb, ub;

  if(
    to_integer(to_constant_expr(arguments[0]), lb) ||
    to_integer(to_constant_expr(arguments[1]), ub))
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
    error() << "'" << identifier << "' expected to have two arguments" << eom;
    throw 0;
  }

  if(lhs.is_nil())
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier << "' expected to have LHS" << eom;
    throw 0;
  }

  side_effect_exprt rhs("prob_coin", lhs.type(), function.source_location());

  if(lhs.type()!=bool_typet())
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier << "' expected bool" << eom;
    throw 0;
  }

  if(arguments[0].type().id()!=ID_unsignedbv ||
     arguments[0].id()!=ID_constant)
  {
    error().source_location=function.find_source_location();
    error() << "'" << identifier << "' expected first operand to be "
            << "a constant literal of type unsigned long" << eom;
    throw 0;
  }

  if(
    arguments[1].type().id() != ID_unsignedbv ||
    arguments[1].id() != ID_constant)
  {
    error().source_location = function.find_source_location();
    error() << "'" << identifier << "' expected second operand to be "
            << "a constant literal of type unsigned long" << eom;
    throw 0;
  }

  mp_integer num, den;

  if(
    to_integer(to_constant_expr(arguments[0]), num) ||
    to_integer(to_constant_expr(arguments[1]), den))
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

  PRECONDITION(f_id == CPROVER_PREFIX "printf");

  codet printf_code(ID_printf, arguments, function.source_location());
  copy(printf_code, OTHER, dest);
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
        const auto type = get_type(t);

        if(type.has_value())
        {
          if(argument_number<arguments.size())
          {
            const typecast_exprt ptr(
              arguments[argument_number], pointer_type(*type));
            argument_number++;

            if(type->id() == ID_array)
            {
              #if 0
              // A string. We first need a nondeterministic size.
              exprt size=side_effect_expr_nondett(size_type());
              to_array_type(*type).size()=size;

              const symbolt &tmp_symbol=
                new_tmp_symbol(
                  *type, "scanf_string", dest, function.source_location());

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
                dereference_exprt{ptr}, from_integer(0, index_type()));
              const side_effect_expr_nondett rhs(
                type->subtype(), function.source_location());
              code_assignt assign(new_lhs, rhs);
              assign.add_source_location()=function.source_location();
              copy(assign, ASSIGN, dest);
              #endif
            }
            else
            {
              // make it nondet for now
              const dereference_exprt new_lhs{ptr};
              const side_effect_expr_nondett rhs(
                *type, function.source_location());
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
  if(arguments.size()<2)
  {
    error().source_location=function.find_source_location();
    error() << "input takes at least two arguments" << eom;
    throw 0;
  }

  copy(code_inputt{arguments, function.source_location()}, OTHER, dest);
}

void goto_convertt::do_output(
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()<2)
  {
    error().source_location=function.find_source_location();
    error() << "output takes at least two arguments" << eom;
    throw 0;
  }

  copy(code_outputt{arguments, function.source_location()}, OTHER, dest);
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

  dest.add(goto_programt::make_atomic_begin(function.source_location()));
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

  dest.add(goto_programt::make_atomic_end(function.source_location()));
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
    count = typecast_exprt::conditional_cast(
      static_cast<const exprt &>(rhs.find(ID_size)), object_size.type());

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
    new_call.arguments().push_back(to_unary_expr(rhs).op()); // memory location
    new_call.set(ID_C_cxx_alloc_type, lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.add_source_location()=rhs.source_location();

    for(std::size_t i=0; i<code_type.parameters().size(); i++)
    {
      new_call.arguments()[i] = typecast_exprt::conditional_cast(
        new_call.arguments()[i], code_type.parameters()[i].type());
    }

    convert(new_call, dest, ID_cpp);
  }
  else
  {
    error().source_location=rhs.find_source_location();
    error() << "cpp_new expected to have 0 or 1 operands" << eom;
    throw 0;
  }

  dest.add(goto_programt::make_assignment(
    lhs,
    typecast_exprt(tmp_symbol_expr, lhs.type()),
    rhs.find_source_location()));

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
    return get_array_argument(to_typecast_expr(src).op());

  if(src.id()!=ID_address_of)
  {
    error().source_location=src.find_source_location();
    error() << "expected array-pointer as argument" << eom;
    throw 0;
  }

  const auto &address_of_expr = to_address_of_expr(src);

  if(address_of_expr.object().id() != ID_index)
  {
    error().source_location=src.find_source_location();
    error() << "expected array-element as argument" << eom;
    throw 0;
  }

  const auto &index_expr = to_index_expr(address_of_expr.object());

  if(index_expr.array().type().id() != ID_array)
  {
    error().source_location=src.find_source_location();
    error() << "expected array as argument" << eom;
    throw 0;
  }

  return index_expr.array();
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
  exprt result = skip_typecast(expr);

  // if it's an address of an lvalue, we take that
  if(result.id() == ID_address_of)
  {
    const auto &address_of_expr = to_address_of_expr(result);
    if(is_assignable(address_of_expr.object()))
      result = address_of_expr.object();
  }

  while(result.type().id() == ID_array &&
        to_array_type(result.type()).size().is_one())
  {
    result = index_exprt{result, from_integer(0, index_type())};
  }

  return result;
}

void goto_convertt::do_enum_is_in_range(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  PRECONDITION(arguments.size() == 1);
  const auto enum_expr = arguments.front();
  const auto enum_type =
    type_try_dynamic_cast<c_enum_tag_typet>(enum_expr.type());
  PRECONDITION(enum_type);
  const c_enum_typet &c_enum_type = ns.follow_tag(*enum_type);
  const c_enum_typet::memberst enum_values = c_enum_type.members();

  exprt::operandst disjuncts;
  for(const auto &enum_value : enum_values)
  {
    constant_exprt val{enum_value.get_value(), *enum_type};
    disjuncts.push_back(equal_exprt(enum_expr, std::move(val)));
  }

  code_assignt assignment(lhs, disjunction(disjuncts));
  assignment.add_source_location() = function.source_location();
  copy(assignment, ASSIGN, dest);
}

void goto_convertt::do_havoc_slice(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest,
  const irep_idt &mode)
{
  irep_idt identifier = CPROVER_PREFIX "havoc_slice";

  // We disable checks on the generated instructions
  // because we add our own rw_ok assertion that takes size into account
  auto source_location = function.find_source_location();
  source_location.add_pragma("disable:pointer-check");
  source_location.add_pragma("disable:pointer-overflow-check");
  source_location.add_pragma("disable:pointer-primitive-check");

  // check # arguments
  if(arguments.size() != 2)
  {
    error().source_location = source_location;
    error() << "'" << identifier << "' expected to have two arguments" << eom;
    throw 0;
  }

  // check argument types
  if(arguments[0].type().id() != ID_pointer)
  {
    error().source_location = source_location;
    error() << "'" << identifier
            << "' first argument expected to have `void *` type" << eom;
    throw 0;
  }

  if(arguments[1].type().id() != ID_unsignedbv)
  {
    error().source_location = source_location;
    error() << "'" << identifier
            << "' second argument expected to have `size_t` type" << eom;
    throw 0;
  }

  // check nil lhs
  if(lhs.is_not_nil())
  {
    error().source_location = source_location;
    error() << "'" << identifier << "' not expected to have a LHS" << eom;
    throw 0;
  }

  // insert instructions
  // assert(rw_ok(argument[0], argument[1]));
  // char nondet_contents[argument[1]];
  // __CPROVER_array_replace(p, nondet_contents);

  r_or_w_ok_exprt ok_expr(ID_w_ok, arguments[0], arguments[1]);
  ok_expr.add_source_location() = source_location;
  goto_programt::targett t =
    dest.add(goto_programt::make_assertion(ok_expr, source_location));
  t->source_location_nonconst().set("user-provided", false);
  t->source_location_nonconst().set_property_class(ID_assertion);
  t->source_location_nonconst().set_comment(
    "assertion havoc_slice " + from_expr(ns, identifier, ok_expr));

  const array_typet array_type(char_type(), arguments[1]);

  const symbolt &nondet_contents =
    new_tmp_symbol(array_type, "nondet_contents", dest, source_location, mode);
  const exprt &nondet_contents_expr = address_of_exprt{
    index_exprt{nondet_contents.symbol_expr(), from_integer(0, index_type())}};

  const exprt &arg0 =
    typecast_exprt::conditional_cast(arguments[0], pointer_type(empty_typet{}));
  const exprt &arg1 = typecast_exprt::conditional_cast(
    nondet_contents_expr, pointer_type(empty_typet{}));

  codet array_replace(ID_array_replace, {arg0, arg1}, source_location);
  dest.add(goto_programt::make_other(array_replace, source_location));
}

/// add function calls to function queue for later processing
void goto_convertt::do_function_call_symbol(
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(function.get_bool(ID_C_invalid_object))
    return; // ignore

  // lookup symbol
  const irep_idt &identifier=function.get_identifier();

  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
  {
    error().source_location=function.find_source_location();
    error() << "error: function '" << identifier << "' not found" << eom;
    throw 0;
  }

  if(symbol->type.id()!=ID_code)
  {
    error().source_location=function.find_source_location();
    error() << "error: function '" << identifier
            << "' type mismatch: expected code" << eom;
    throw 0;
  }

  // User-provided function definitions always take precedence over built-ins.
  // Front-ends do not (yet) consistently set ID_C_incomplete, thus also test
  // whether the symbol actually has some non-nil value (which might be
  // "compiled").
  if(!symbol->type.get_bool(ID_C_incomplete) && symbol->value.is_not_nil())
  {
    do_function_call_symbol(*symbol);

    code_function_callt function_call(lhs, function, arguments);
    function_call.add_source_location() = function.source_location();

    copy(function_call, FUNCTION_CALL, dest);

    return;
  }

  if(identifier == CPROVER_PREFIX "havoc_slice")
  {
    do_havoc_slice(lhs, function, arguments, dest, mode);
  }
  else if(
    identifier == CPROVER_PREFIX "assume" || identifier == "__VERIFIER_assume")
  {
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have one argument" << eom;
      throw 0;
    }

    // let's double-check the type of the argument
    goto_programt::targett t = dest.add(goto_programt::make_assumption(
      typecast_exprt::conditional_cast(arguments.front(), bool_typet()),
      function.source_location()));

    t->source_location_nonconst().set("user-provided", true);

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
      error() << "'" << identifier << "' expected to have no arguments" << eom;
      throw 0;
    }

    goto_programt::targett t = dest.add(
      goto_programt::make_assertion(false_exprt(), function.source_location()));

    t->source_location_nonconst().set("user-provided", true);
    t->source_location_nonconst().set_property_class(ID_assertion);

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }

    // __VERIFIER_error has abort() semantics, even if no assertions
    // are being checked
    goto_programt::targett a = dest.add(goto_programt::make_assumption(
      false_exprt(), function.source_location()));
    a->source_location_nonconst().set("user-provided", true);
  }
  else if(
    identifier == "assert" &&
    to_code_type(symbol->type).return_type() == signed_int_type())
  {
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have one argument" << eom;
      throw 0;
    }

    // let's double-check the type of the argument
    goto_programt::targett t = dest.add(goto_programt::make_assertion(
      typecast_exprt::conditional_cast(arguments.front(), bool_typet()),
      function.source_location()));
    t->source_location_nonconst().set("user-provided", true);
    t->source_location_nonconst().set_property_class(ID_assertion);
    t->source_location_nonconst().set_comment(
      "assertion " + from_expr(ns, identifier, arguments.front()));

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }
  }
  else if(identifier == CPROVER_PREFIX "enum_is_in_range")
  {
    do_enum_is_in_range(lhs, function, arguments, dest);
  }
  else if(
    identifier == CPROVER_PREFIX "assert" ||
    identifier == CPROVER_PREFIX "precondition" ||
    identifier == CPROVER_PREFIX "postcondition")
  {
    if(arguments.size()!=2)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have two arguments" << eom;
      throw 0;
    }

    bool is_precondition=
      identifier==CPROVER_PREFIX "precondition";
    bool is_postcondition = identifier == CPROVER_PREFIX "postcondition";

    const irep_idt description=
      get_string_constant(arguments[1]);

    // let's double-check the type of the argument
    goto_programt::targett t = dest.add(goto_programt::make_assertion(
      typecast_exprt::conditional_cast(arguments[0], bool_typet()),
      function.source_location()));

    if(is_precondition)
    {
      t->source_location_nonconst().set_property_class(ID_precondition);
    }
    else if(is_postcondition)
    {
      t->source_location_nonconst().set_property_class(ID_postcondition);
    }
    else
    {
      t->source_location_nonconst().set(
        "user-provided", !function.source_location().is_built_in());
      t->source_location_nonconst().set_property_class(ID_assertion);
    }

    t->source_location_nonconst().set_comment(description);

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
      error() << "'" << identifier << "' expected to have one argument" << eom;
      throw 0;
    }

    if(lhs.is_not_nil())
    {
      error().source_location=function.find_source_location();
      error() << identifier << " expected not to have LHS" << eom;
      throw 0;
    }

    codet havoc(ID_havoc_object);
    havoc.add_source_location() = function.source_location();
    havoc.copy_to_operands(arguments[0]);

    dest.add(goto_programt::make_other(havoc, function.source_location()));
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

    if(function.type().get_bool(ID_C_incomplete))
    {
      error().source_location = function.find_source_location();
      error() << "'" << identifier << "' is not declared, "
              << "missing type information required to construct call to "
              << "uninterpreted function" << eom;
      throw 0;
    }

    const code_typet &function_call_type = to_code_type(function.type());
    mathematical_function_typet::domaint domain;
    for(const auto &parameter : function_call_type.parameters())
      domain.push_back(parameter.type());
    mathematical_function_typet function_type{domain,
                                              function_call_type.return_type()};
    const function_application_exprt rhs(
      symbol_exprt{function.get_identifier(), function_type}, arguments);

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
      error() << "'" << identifier << "' expected to have four arguments"
              << eom;
      throw 0;
    }

    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    goto_programt::targett t = dest.add(
      goto_programt::make_assertion(false_exprt(), function.source_location()));

    t->source_location_nonconst().set("user-provided", true);
    t->source_location_nonconst().set_property_class(ID_assertion);
    t->source_location_nonconst().set_comment(description);
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
      error() << "'" << identifier << "' expected to have four arguments"
              << eom;
      throw 0;
    }

    goto_programt::targett t = dest.add(
      goto_programt::make_assertion(false_exprt(), function.source_location()));

    t->source_location_nonconst().set("user-provided", true);
    t->source_location_nonconst().set_property_class(ID_assertion);
    t->source_location_nonconst().set_comment(description);
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
      error() << "'" << identifier << "' expected to have four arguments"
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

    goto_programt::targett t = dest.add(
      goto_programt::make_assertion(false_exprt(), function.source_location()));

    t->source_location_nonconst().set("user-provided", true);
    t->source_location_nonconst().set_property_class(ID_assertion);
    t->source_location_nonconst().set_comment(description);
    // we ignore any LHS
  }
  else if(identifier==CPROVER_PREFIX "fence")
  {
    if(arguments.empty())
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have at least one argument"
              << eom;
      throw 0;
    }

    codet fence(ID_fence);

    for(const auto &argument : arguments)
      fence.set(get_string_constant(argument), true);

    dest.add(goto_programt::make_other(fence, function.source_location()));
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
    // 1) Return value of argument.
    //    This is just dereferencing.
    // 2) Move list pointer to next argument.
    //    This is just an increment.

    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have one argument" << eom;
      throw 0;
    }

    exprt list_arg=make_va_list(arguments[0]);

    if(lhs.is_not_nil())
    {
      exprt list_arg_cast = list_arg;
      if(
        list_arg.type().id() == ID_pointer &&
        to_pointer_type(list_arg.type()).subtype().id() == ID_empty)
      {
        list_arg_cast =
          typecast_exprt{list_arg, pointer_type(pointer_type(empty_typet{}))};
      }

      typet t=pointer_type(lhs.type());
      dereference_exprt rhs{
        typecast_exprt{dereference_exprt{std::move(list_arg_cast)}, t}};
      rhs.add_source_location()=function.source_location();
      dest.add(
        goto_programt::make_assignment(lhs, rhs, function.source_location()));
    }

    code_assignt assign{
      list_arg, plus_exprt{list_arg, from_integer(1, pointer_diff_type())}};
    assign.rhs().set(
      ID_C_va_arg_type, to_code_type(function.type()).return_type());
    dest.add(goto_programt::make_assignment(
      std::move(assign), function.source_location()));
  }
  else if(identifier=="__builtin_va_copy")
  {
    if(arguments.size()!=2)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have two arguments" << eom;
      throw 0;
    }

    exprt dest_expr=make_va_list(arguments[0]);
    const typecast_exprt src_expr(arguments[1], dest_expr.type());

    if(!is_assignable(dest_expr))
    {
      error().source_location=dest_expr.find_source_location();
      error() << "va_copy argument expected to be lvalue" << eom;
      throw 0;
    }

    dest.add(goto_programt::make_assignment(
      dest_expr, src_expr, function.source_location()));
  }
  else if(identifier == "__builtin_va_start" || identifier == "__va_start")
  {
    // Set the list argument to be the address of the
    // parameter argument.
    if(arguments.size()!=2)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have two arguments" << eom;
      throw 0;
    }

    exprt dest_expr=make_va_list(arguments[0]);

    if(!is_assignable(dest_expr))
    {
      error().source_location=dest_expr.find_source_location();
      error() << "va_start argument expected to be lvalue" << eom;
      throw 0;
    }

    if(
      dest_expr.type().id() == ID_pointer &&
      to_pointer_type(dest_expr.type()).subtype().id() == ID_empty)
    {
      dest_expr =
        typecast_exprt{dest_expr, pointer_type(pointer_type(empty_typet{}))};
    }

    side_effect_exprt rhs{
      ID_va_start, dest_expr.type(), function.source_location()};
    rhs.add_to_operands(
      typecast_exprt{address_of_exprt{arguments[1]}, dest_expr.type()});

    dest.add(goto_programt::make_assignment(
      std::move(dest_expr), std::move(rhs), function.source_location()));
  }
  else if(identifier=="__builtin_va_end")
  {
    // Invalidates the argument. We do so by setting it to NULL.
    if(arguments.size()!=1)
    {
      error().source_location=function.find_source_location();
      error() << "'" << identifier << "' expected to have one argument" << eom;
      throw 0;
    }

    exprt dest_expr=make_va_list(arguments[0]);

    if(!is_assignable(dest_expr))
    {
      error().source_location=dest_expr.find_source_location();
      error() << "va_end argument expected to be lvalue" << eom;
      throw 0;
    }

    // our __builtin_va_list is a pointer
    if(dest_expr.type().id() == ID_pointer)
    {
      const auto zero =
        zero_initializer(dest_expr.type(), function.source_location(), ns);
      CHECK_RETURN(zero.has_value());
      dest.add(goto_programt::make_assignment(
        dest_expr, *zero, function.source_location()));
    }
  }
  else if(
    identifier == "__builtin_isgreater" ||
    identifier == "__builtin_isgreaterequal" ||
    identifier == "__builtin_isless" || identifier == "__builtin_islessequal" ||
    identifier == "__builtin_islessgreater" ||
    identifier == "__builtin_isunordered")
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
      error() << "'" << identifier
              << "' expected to have two float/double arguments" << eom;
      throw 0;
    }

    exprt::operandst new_arguments=arguments;

    bool use_double=arguments[0].type()==double_type();
    if(arguments[0].type()!=arguments[1].type())
    {
      if(use_double)
      {
        new_arguments[1] =
          typecast_exprt(new_arguments[1], arguments[0].type());
      }
      else
      {
        new_arguments[0] =
          typecast_exprt(new_arguments[0], arguments[1].type());
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
