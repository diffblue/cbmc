/*******************************************************************\

Module: Remove 'vector' data type

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

/// \file
/// Remove 'vector' data type

#include "remove_vector.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "goto_model.h"

static bool have_to_remove_vector(const typet &type);

static bool have_to_remove_vector(const exprt &expr)
{
  if(expr.type().id()==ID_vector)
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div ||
       expr.id()==ID_mod  || expr.id()==ID_bitxor ||
       expr.id()==ID_bitand || expr.id()==ID_bitor)
      return true;
    else if(expr.id()==ID_unary_minus || expr.id()==ID_bitnot)
      return true;
    else if(expr.id()==ID_vector)
      return true;
  }

  if(have_to_remove_vector(expr.type()))
    return true;

  forall_operands(it, expr)
    if(have_to_remove_vector(*it))
      return true;

  return false;
}

static bool have_to_remove_vector(const typet &type)
{
  if(type.id()==ID_struct || type.id()==ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(have_to_remove_vector(c.type()))
        return true;
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_complex ||
          type.id()==ID_array)
    return have_to_remove_vector(type.subtype());
  else if(type.id()==ID_vector)
    return true;

  return false;
}

/// removes vector data type
static void remove_vector(typet &);

static void remove_vector(exprt &expr)
{
  if(!have_to_remove_vector(expr))
    return;

  Forall_operands(it, expr)
    remove_vector(*it);

  if(expr.type().id()==ID_vector)
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div ||
       expr.id()==ID_mod  || expr.id()==ID_bitxor ||
       expr.id()==ID_bitand || expr.id()==ID_bitor)
    {
      // FIXME plus, mult, bitxor, bitand and bitor are defined as n-ary
      //      operations rather than binary. This code assumes that they
      //      can only have exactly 2 operands, and it is not clear
      //      that it is safe to do so in this context
      PRECONDITION(expr.operands().size() == 2);
      auto const &binary_expr = to_binary_expr(expr);
      remove_vector(expr.type());
      array_typet array_type=to_array_type(expr.type());

      const mp_integer dimension =
        numeric_cast_v<mp_integer>(array_type.size());

      const typet subtype=array_type.subtype();
      // do component-wise:
      // x+y -> vector(x[0]+y[0],x[1]+y[1],...)
      array_exprt array_expr(array_type);
      array_expr.operands().resize(numeric_cast_v<std::size_t>(dimension));

      for(std::size_t i=0; i<array_expr.operands().size(); i++)
      {
        exprt index=from_integer(i, array_type.size().type());

        array_expr.operands()[i] = binary_exprt(
          index_exprt(binary_expr.op0(), index, subtype),
          binary_expr.id(),
          index_exprt(binary_expr.op1(), index, subtype));
      }

      expr=array_expr;
    }
    else if(expr.id()==ID_unary_minus || expr.id()==ID_bitnot)
    {
      auto const &unary_expr = to_unary_expr(expr);
      remove_vector(expr.type());
      array_typet array_type=to_array_type(expr.type());

      const mp_integer dimension =
        numeric_cast_v<mp_integer>(array_type.size());

      const typet subtype=array_type.subtype();
      // do component-wise:
      // -x -> vector(-x[0],-x[1],...)
      array_exprt array_expr(array_type);
      array_expr.operands().resize(numeric_cast_v<std::size_t>(dimension));

      for(std::size_t i=0; i<array_expr.operands().size(); i++)
      {
        exprt index=from_integer(i, array_type.size().type());

        array_expr.operands()[i] = unary_exprt(
          unary_expr.id(), index_exprt(unary_expr.op0(), index, subtype));
      }

      expr=array_expr;
    }
    else if(expr.id()==ID_vector)
    {
      expr.id(ID_array);
    }
    else if(expr.id() == ID_typecast)
    {
      const auto &op = to_typecast_expr(expr).op();

      if(op.type().id() != ID_array)
      {
        // (vector-type) x ==> { x, x, ..., x }
        remove_vector(expr.type());
        array_typet array_type = to_array_type(expr.type());
        const auto dimension = numeric_cast_v<std::size_t>(array_type.size());
        exprt casted_op =
          typecast_exprt::conditional_cast(op, array_type.subtype());
        array_exprt array_expr(array_type);
        array_expr.operands().resize(dimension, op);
        expr = array_expr;
      }
    }
  }

  remove_vector(expr.type());
}

/// removes vector data type
static void remove_vector(typet &type)
{
  if(!have_to_remove_vector(type))
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
      remove_vector(it->type());
    }
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_complex ||
          type.id()==ID_array)
  {
    remove_vector(type.subtype());
  }
  else if(type.id()==ID_vector)
  {
    vector_typet &vector_type=to_vector_type(type);

    remove_vector(type.subtype());

    // Replace by an array with appropriate number of members.
    array_typet array_type(vector_type.subtype(), vector_type.size());
    array_type.add_source_location()=type.source_location();
    type=array_type;
  }
}

/// removes vector data type
static void remove_vector(symbolt &symbol)
{
  remove_vector(symbol.value);
  remove_vector(symbol.type);
}

/// removes vector data type
static void remove_vector(symbol_tablet &symbol_table)
{
  for(const auto &named_symbol : symbol_table.symbols)
    remove_vector(*symbol_table.get_writeable(named_symbol.first));
}

/// removes vector data type
void remove_vector(goto_functionst::goto_functiont &goto_function)
{
  remove_vector(goto_function.type);

  Forall_goto_program_instructions(it, goto_function.body)
  {
    remove_vector(it->code);
    remove_vector(it->guard);
  }
}

/// removes vector data type
static void remove_vector(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    remove_vector(it->second);
}

/// removes vector data type
void remove_vector(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_vector(symbol_table);
  remove_vector(goto_functions);
}

/// removes vector data type
void remove_vector(goto_modelt &goto_model)
{
  remove_vector(goto_model.symbol_table, goto_model.goto_functions);
}
