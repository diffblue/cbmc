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

#include <ansi-c/c_expr.h>

#include "goto_model.h"

static bool have_to_remove_vector(const typet &type);

static bool have_to_remove_vector(const exprt &expr)
{
  if(expr.type().id()==ID_vector)
  {
    if(
      expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
      expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_bitxor ||
      expr.id() == ID_bitand || expr.id() == ID_bitor || expr.id() == ID_shl ||
      expr.id() == ID_lshr || expr.id() == ID_ashr ||
      expr.id() == ID_saturating_minus || expr.id() == ID_saturating_plus)
    {
      return true;
    }
    else if(expr.id()==ID_unary_minus || expr.id()==ID_bitnot)
      return true;
    else if(
      expr.id() == ID_vector_equal || expr.id() == ID_vector_notequal ||
      expr.id() == ID_vector_lt || expr.id() == ID_vector_le ||
      expr.id() == ID_vector_gt || expr.id() == ID_vector_ge)
    {
      return true;
    }
    else if(expr.id() == ID_shuffle_vector)
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
  else if(type.id() == ID_code)
  {
    const code_typet &code_type = to_code_type(type);

    if(have_to_remove_vector(code_type.return_type()))
      return true;
    for(auto &parameter : code_type.parameters())
    {
      if(have_to_remove_vector(parameter.type()))
        return true;
    }
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_complex ||
          type.id()==ID_array)
    return have_to_remove_vector(to_type_with_subtype(type).subtype());
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

  if(expr.id() == ID_shuffle_vector)
  {
    exprt result = to_shuffle_vector_expr(expr).lower();
    remove_vector(result);
    expr.swap(result);
    return;
  }

  Forall_operands(it, expr)
    remove_vector(*it);

  if(expr.type().id()==ID_vector)
  {
    if(
      expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
      expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_bitxor ||
      expr.id() == ID_bitand || expr.id() == ID_bitor || expr.id() == ID_shl ||
      expr.id() == ID_lshr || expr.id() == ID_ashr ||
      expr.id() == ID_saturating_minus || expr.id() == ID_saturating_plus)
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
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));

      const typet subtype = array_type.element_type();
      // do component-wise:
      // x+y -> vector(x[0]+y[0],x[1]+y[1],...)
      array_exprt array_expr({}, array_type);
      array_expr.operands().resize(numeric_cast_v<std::size_t>(dimension));
      array_expr.add_source_location() = expr.source_location();

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
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));

      const typet subtype = array_type.element_type();
      // do component-wise:
      // -x -> vector(-x[0],-x[1],...)
      array_exprt array_expr({}, array_type);
      array_expr.operands().resize(numeric_cast_v<std::size_t>(dimension));
      array_expr.add_source_location() = expr.source_location();

      for(std::size_t i=0; i<array_expr.operands().size(); i++)
      {
        exprt index=from_integer(i, array_type.size().type());

        array_expr.operands()[i] = unary_exprt(
          unary_expr.id(), index_exprt(unary_expr.op(), index, subtype));
      }

      expr=array_expr;
    }
    else if(
      expr.id() == ID_vector_equal || expr.id() == ID_vector_notequal ||
      expr.id() == ID_vector_lt || expr.id() == ID_vector_le ||
      expr.id() == ID_vector_gt || expr.id() == ID_vector_ge)
    {
      // component-wise and generate 0 (false) or -1 (true)
      // x ~ y -> vector(x[0] ~ y[0] ? -1 : 0, x[1] ~ y[1] ? -1 : 0, ...)

      auto const &binary_expr = to_binary_expr(expr);
      const vector_typet &vector_type = to_vector_type(expr.type());
      const auto dimension = numeric_cast_v<std::size_t>(vector_type.size());

      const typet &subtype = vector_type.element_type();
      PRECONDITION(subtype.id() == ID_signedbv);
      exprt minus_one = from_integer(-1, subtype);
      exprt zero = from_integer(0, subtype);

      exprt::operandst operands;
      operands.reserve(dimension);

      const bool is_float =
        to_array_type(binary_expr.lhs().type()).element_type().id() ==
        ID_floatbv;
      irep_idt new_id;
      if(binary_expr.id() == ID_vector_notequal)
      {
        if(is_float)
          new_id = ID_ieee_float_notequal;
        else
          new_id = ID_notequal;
      }
      else if(binary_expr.id() == ID_vector_equal)
      {
        if(is_float)
          new_id = ID_ieee_float_equal;
        else
          new_id = ID_equal;
      }
      else
      {
        // just strip the "vector-" prefix
        new_id = id2string(binary_expr.id()).substr(7);
      }

      for(std::size_t i = 0; i < dimension; ++i)
      {
        exprt index = from_integer(i, vector_type.size().type());

        operands.push_back(
          if_exprt{binary_relation_exprt{index_exprt{binary_expr.lhs(), index},
                                         new_id,
                                         index_exprt{binary_expr.rhs(), index}},
                   minus_one,
                   zero});
      }

      source_locationt source_location = expr.source_location();
      expr = array_exprt{std::move(operands),
                         array_typet{subtype, vector_type.size()}};
      expr.add_source_location() = std::move(source_location);
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
        const auto dimension =
          numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
        exprt casted_op =
          typecast_exprt::conditional_cast(op, array_type.element_type());
        source_locationt source_location = expr.source_location();
        expr = array_exprt(exprt::operandst(dimension, casted_op), array_type);
        expr.add_source_location() = std::move(source_location);
      }
      else if(
        expr.type().id() == ID_vector &&
        to_vector_type(expr.type()).size() == to_array_type(op.type()).size())
      {
        // do component-wise typecast:
        // (vector-type) x -> array((vector-sub-type)x[0], ...)
        remove_vector(expr.type());
        const array_typet &array_type = to_array_type(expr.type());
        const std::size_t dimension =
          numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
        const typet subtype = array_type.element_type();

        exprt::operandst elements;
        elements.reserve(dimension);

        for(std::size_t i = 0; i < dimension; i++)
        {
          exprt index = from_integer(i, array_type.size().type());
          elements.push_back(
            typecast_exprt{index_exprt{op, std::move(index)}, subtype});
        }

        array_exprt array_expr(std::move(elements), array_type);
        array_expr.add_source_location() = expr.source_location();
        expr.swap(array_expr);
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
  else if(type.id() == ID_code)
  {
    code_typet &code_type = to_code_type(type);

    remove_vector(code_type.return_type());
    for(auto &parameter : code_type.parameters())
      remove_vector(parameter.type());
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

    remove_vector(vector_type.element_type());

    // Replace by an array with appropriate number of members.
    array_typet array_type(vector_type.element_type(), vector_type.size());
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
    remove_vector(symbol_table.get_writeable_ref(named_symbol.first));
}

/// removes vector data type
void remove_vector(goto_functionst::goto_functiont &goto_function)
{
  for(auto &i : goto_function.body.instructions)
    i.transform([](exprt e) -> optionalt<exprt> {
      if(have_to_remove_vector(e))
      {
        remove_vector(e);
        return e;
      }
      else
        return {};
    });
}

/// removes vector data type
static void remove_vector(goto_functionst &goto_functions)
{
  for(auto &gf_entry : goto_functions.function_map)
    remove_vector(gf_entry.second);
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
