/*******************************************************************\

Module: Remove 'complex' data type

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

/// \file
/// Remove 'complex' data type

#include "remove_complex.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include "goto_model.h"

static exprt complex_member(const exprt &expr, irep_idt id)
{
  if(expr.id()==ID_struct && expr.operands().size()==2)
  {
    if(id==ID_real)
      return to_binary_expr(expr).op0();
    else if(id==ID_imag)
      return to_binary_expr(expr).op1();
    else
      UNREACHABLE;
  }
  else
  {
    const struct_typet &struct_type=
      to_struct_type(expr.type());
    PRECONDITION(struct_type.components().size() == 2);
    return member_exprt(expr, id, struct_type.components().front().type());
  }
}

static bool have_to_remove_complex(const typet &type);

static bool have_to_remove_complex(const exprt &expr)
{
  if(expr.id()==ID_typecast &&
     to_typecast_expr(expr).op().type().id()==ID_complex &&
     expr.type().id()!=ID_complex)
    return true;

  if(expr.type().id()==ID_complex)
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div)
      return true;
    else if(expr.id()==ID_unary_minus)
      return true;
    else if(expr.id()==ID_complex)
      return true;
    else if(expr.id()==ID_typecast)
      return true;
  }

  if(expr.id()==ID_complex_real)
    return true;
  else if(expr.id()==ID_complex_imag)
    return true;

  if(have_to_remove_complex(expr.type()))
     return true;

  for(const auto &op : expr.operands())
  {
    if(have_to_remove_complex(op))
      return true;
  }

  return false;
}

static bool have_to_remove_complex(const typet &type)
{
  if(type.id()==ID_struct || type.id()==ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(have_to_remove_complex(c.type()))
        return true;
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_vector ||
          type.id()==ID_array)
    return have_to_remove_complex(to_type_with_subtype(type).subtype());
  else if(type.id()==ID_complex)
    return true;

  return false;
}

/// removes complex data type
static void remove_complex(typet &);

static void remove_complex(exprt &expr)
{
  if(!have_to_remove_complex(expr))
    return;

  if(expr.id()==ID_typecast)
  {
    auto const &typecast_expr = to_typecast_expr(expr);
    if(typecast_expr.op().type().id() == ID_complex)
    {
      if(typecast_expr.type().id() == ID_complex)
      {
        // complex to complex
      }
      else
      {
        // cast complex to non-complex is (T)__real__ x
        complex_real_exprt complex_real_expr(typecast_expr.op());

        expr = typecast_exprt(complex_real_expr, typecast_expr.type());
      }
    }
  }

  Forall_operands(it, expr)
    remove_complex(*it);

  if(expr.type().id()==ID_complex)
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div)
    {
      // FIXME plus and mult are defined as n-ary operations
      //      rather than binary. This code assumes that they
      //      can only have exactly 2 operands, and it is not clear
      //      that it is safe to do so in this context
      PRECONDITION(expr.operands().size() == 2);
      // do component-wise:
      // x+y -> complex(x.r+y.r,x.i+y.i)
      struct_exprt struct_expr(
        {binary_exprt(
           complex_member(to_binary_expr(expr).op0(), ID_real),
           expr.id(),
           complex_member(to_binary_expr(expr).op1(), ID_real)),
         binary_exprt(
           complex_member(to_binary_expr(expr).op0(), ID_imag),
           expr.id(),
           complex_member(to_binary_expr(expr).op1(), ID_imag))},
        expr.type());

      struct_expr.op0().add_source_location() = expr.source_location();
      struct_expr.op1().add_source_location()=expr.source_location();

      expr=struct_expr;
    }
    else if(expr.id()==ID_unary_minus)
    {
      auto const &unary_minus_expr = to_unary_minus_expr(expr);
      // do component-wise:
      // -x -> complex(-x.r,-x.i)
      struct_exprt struct_expr(
        {unary_minus_exprt(complex_member(unary_minus_expr.op(), ID_real)),
         unary_minus_exprt(complex_member(unary_minus_expr.op(), ID_imag))},
        unary_minus_expr.type());

      struct_expr.op0().add_source_location() =
        unary_minus_expr.source_location();

      struct_expr.op1().add_source_location() =
        unary_minus_expr.source_location();

      expr=struct_expr;
    }
    else if(expr.id()==ID_complex)
    {
      auto const &complex_expr = to_complex_expr(expr);
      auto struct_expr = struct_exprt(
        {complex_expr.real(), complex_expr.imag()}, complex_expr.type());
      struct_expr.add_source_location() = complex_expr.source_location();
      expr.swap(struct_expr);
    }
    else if(expr.id()==ID_typecast)
    {
      auto const &typecast_expr = to_typecast_expr(expr);
      typet subtype = to_complex_type(typecast_expr.type()).subtype();

      if(typecast_expr.op().type().id() == ID_struct)
      {
        // complex to complex -- do typecast per component

        struct_exprt struct_expr(
          {typecast_exprt(complex_member(typecast_expr.op(), ID_real), subtype),
           typecast_exprt(
             complex_member(typecast_expr.op(), ID_imag), subtype)},
          typecast_expr.type());

        struct_expr.op0().add_source_location() =
          typecast_expr.source_location();

        struct_expr.op1().add_source_location() =
          typecast_expr.source_location();

        expr=struct_expr;
      }
      else
      {
        // non-complex to complex
        struct_exprt struct_expr(
          {typecast_exprt(typecast_expr.op(), subtype),
           from_integer(0, subtype)},
          typecast_expr.type());
        struct_expr.add_source_location() = typecast_expr.source_location();

        expr=struct_expr;
      }
    }
  }

  if(expr.id()==ID_complex_real)
  {
    expr = complex_member(to_complex_real_expr(expr).op(), ID_real);
  }
  else if(expr.id()==ID_complex_imag)
  {
    expr = complex_member(to_complex_imag_expr(expr).op(), ID_imag);
  }

  remove_complex(expr.type());
}

/// removes complex data type
static void remove_complex(typet &type)
{
  if(!have_to_remove_complex(type))
    return;

  if(type.id()==ID_struct || type.id()==ID_union)
  {
    struct_union_typet &struct_union_type=
      to_struct_union_type(type);
    for(struct_union_typet::componentst::iterator
        it=struct_union_type.components().begin();
        it!=struct_union_type.components().end();
        it++)
    {
      remove_complex(it->type());
    }
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_vector ||
          type.id()==ID_array)
  {
    remove_complex(to_type_with_subtype(type).subtype());
  }
  else if(type.id()==ID_complex)
  {
    remove_complex(to_complex_type(type).subtype());

    // Replace by a struct with two members.
    // The real part goes first.
    struct_typet struct_type(
      {{ID_real, to_complex_type(type).subtype()},
       {ID_imag, to_complex_type(type).subtype()}});
    struct_type.add_source_location()=type.source_location();

    type = std::move(struct_type);
  }
}

/// removes complex data type
static void remove_complex(symbolt &symbol)
{
  remove_complex(symbol.value);
  remove_complex(symbol.type);
}

/// removes complex data type
void remove_complex(symbol_tablet &symbol_table)
{
  for(const auto &named_symbol : symbol_table.symbols)
    remove_complex(symbol_table.get_writeable_ref(named_symbol.first));
}

/// removes complex data type
static void remove_complex(
  goto_functionst::goto_functiont &goto_function)
{
  for(auto &i : goto_function.body.instructions)
    i.transform([](exprt e) -> optionalt<exprt> {
      if(have_to_remove_complex(e))
      {
        remove_complex(e);
        return e;
      }
      else
        return {};
    });
}

/// removes complex data type
static void remove_complex(goto_functionst &goto_functions)
{
  for(auto &gf_entry : goto_functions.function_map)
    remove_complex(gf_entry.second);
}

/// removes complex data type
void remove_complex(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_complex(symbol_table);
  remove_complex(goto_functions);
  add_history_transform(goto_transform_kindt::remove_complex, goto_functions);
}

/// removes complex data type
void remove_complex(goto_modelt &goto_model)
{
  remove_complex(goto_model.symbol_table, goto_model.goto_functions);
}
