/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/simplify_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

/// Replace symbol expressions that refer to constant variables with their
/// compile-time values, enabling constant folding in static_assert.
void cpp_typecheckt::propagate_constants(
  exprt &expr,
  const symbol_table_baset &symbol_table)
{
  if(expr.id() == ID_symbol)
  {
    const symbolt *s =
      symbol_table.lookup(to_symbol_expr(expr).get_identifier());
    // A const object with a value, or a constexpr object (a macro, e.g. a
    // constexpr object of class type, [dcl.constexpr]/6): substitute its
    // value so a member read `g.v` or a member function call folds in a
    // constant expression.
    if(
      s != nullptr && s->value.is_not_nil() &&
      (s->type.get_bool(ID_C_constant) ||
       (s->is_macro && !s->is_type && s->type.id() != ID_code)))
    {
      expr = s->value;
      return;
    }
  }

  for(auto &op : expr.operands())
    propagate_constants(op, symbol_table);
}

void cpp_typecheckt::convert(cpp_static_assertt &cpp_static_assert)
{
  {
    // The static_assert condition is a constant expression ([dcl.pre]).
    constant_expression_contextt constant_expression_guard{*this};
    typecheck_expr(cpp_static_assert.op0());
  }
  typecheck_expr(cpp_static_assert.op1());

  implicit_typecast_bool(cpp_static_assert.op0());

  propagate_constants(cpp_static_assert.op0(), symbol_table);

  simplify(cpp_static_assert.op0(), *this);

  // N5008 [dcl.pre]/10: the condition is a constant expression; if our
  // constant evaluation falls short the check is dropped.  Say so for the
  // user's own code, as the block-scope form (typecheck_code) does -- a
  // silently skipped assertion hid several evaluation gaps.  Library
  // headers are full of assertions over traits we do not model; those, and
  // assertions inside a template instantiation (which may be a "no valid
  // specialization" guard, [temp.res.general]/6), stay quiet.
  if(!cpp_static_assert.op0().is_constant())
  {
    const std::string file =
      id2string(cpp_static_assert.source_location().get_file());
    if(
      instantiation_stack.empty() && !file.empty() &&
      !is_library_body_file(file) && file.find("<built") != 0)
    {
      warning().source_location = cpp_static_assert.source_location();
      warning() << "static_assert condition could not be evaluated; the "
                << "assertion is not checked" << eom;
    }
    return;
  }

  if(cpp_static_assert.op0() == false_exprt())
  {
    // failed
    error().source_location=cpp_static_assert.source_location();
    error() << "static assertion failed";
    if(cpp_static_assert.op1().id()==ID_string_constant)
      error() << ": " << to_string_constant(cpp_static_assert.op1()).value();
    error() << eom;
    throw 0;
  }
}
