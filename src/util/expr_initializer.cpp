/*******************************************************************\

Module: Expression Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Initialization

#include "expr_initializer.h"

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "byte_operators.h"
#include "c_types.h"
#include "config.h"
#include "magic.h"
#include "namespace.h" // IWYU pragma: keep
#include "simplify_expr.h"
#include "std_code.h"
#include "symbol_table.h"

class expr_initializert
{
public:
  explicit expr_initializert(const namespacet &_ns) : ns(_ns)
  {
  }

  std::optional<exprt> operator()(
    const typet &type,
    const source_locationt &source_location,
    const exprt &init_expr)
  {
    return expr_initializer_rec(type, source_location, init_expr);
  }

protected:
  const namespacet &ns;

  std::optional<exprt> expr_initializer_rec(
    const typet &type,
    const source_locationt &source_location,
    const exprt &init_expr);
};

std::optional<exprt> expr_initializert::expr_initializer_rec(
  const typet &type,
  const source_locationt &source_location,
  const exprt &init_expr)
{
  const irep_idt &type_id=type.id();

  if(type_id==ID_unsignedbv ||
     type_id==ID_signedbv ||
     type_id==ID_pointer ||
     type_id==ID_c_enum ||
     type_id==ID_c_bit_field ||
     type_id==ID_bool ||
     type_id==ID_c_bool ||
     type_id==ID_floatbv ||
     type_id==ID_fixedbv)
  {
    exprt result;
    if(init_expr.id() == ID_nondet)
      result = side_effect_expr_nondett(type, source_location);
    else if(init_expr.is_zero())
      result = from_integer(0, type);
    else
      result = duplicate_per_byte(init_expr, type, ns);

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_rational ||
          type_id==ID_real)
  {
    exprt result;
    if(init_expr.id() == ID_nondet)
      result = side_effect_expr_nondett(type, source_location);
    else if(init_expr.is_zero())
      result = constant_exprt(ID_0, type);
    else
      result = duplicate_per_byte(init_expr, type, ns);

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_verilog_signedbv ||
          type_id==ID_verilog_unsignedbv)
  {
    exprt result;
    if(init_expr.id() == ID_nondet)
      result = side_effect_expr_nondett(type, source_location);
    else if(init_expr.is_zero())
    {
      const std::size_t width = to_bitvector_type(type).get_width();
      std::string value(width, '0');

      result = constant_exprt(value, type);
    }
    else
      result = duplicate_per_byte(init_expr, type, ns);

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_complex)
  {
    exprt result;
    if(init_expr.id() == ID_nondet)
      result = side_effect_expr_nondett(type, source_location);
    else if(init_expr.is_zero())
    {
      auto sub_zero = expr_initializer_rec(
        to_complex_type(type).subtype(), source_location, init_expr);
      if(!sub_zero.has_value())
        return {};

      result = complex_exprt(*sub_zero, *sub_zero, to_complex_type(type));
    }
    else
      result = duplicate_per_byte(init_expr, type, ns);

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_array)
  {
    const array_typet &array_type=to_array_type(type);

    if(array_type.size().is_nil())
    {
      // we initialize this with an empty array

      array_exprt value({}, array_type);
      value.type().size() = from_integer(0, size_type());
      value.add_source_location()=source_location;
      return std::move(value);
    }
    else
    {
      auto tmpval = expr_initializer_rec(
        array_type.element_type(), source_location, init_expr);
      if(!tmpval.has_value())
        return {};

      const auto array_size = numeric_cast<mp_integer>(array_type.size());
      if(
        array_type.size().id() == ID_infinity || !array_size.has_value() ||
        *array_size > MAX_FLATTENED_ARRAY_SIZE)
      {
        if(init_expr.id() == ID_nondet)
          return side_effect_expr_nondett(type, source_location);

        array_of_exprt value(*tmpval, array_type);
        value.add_source_location()=source_location;
        return std::move(value);
      }

      if(*array_size < 0)
        return {};

      array_exprt value({}, array_type);
      value.operands().resize(
        numeric_cast_v<std::size_t>(*array_size), *tmpval);
      value.add_source_location()=source_location;
      return std::move(value);
    }
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);

    auto tmpval = expr_initializer_rec(
      vector_type.element_type(), source_location, init_expr);
    if(!tmpval.has_value())
      return {};

    const mp_integer vector_size =
      numeric_cast_v<mp_integer>(vector_type.size());

    if(vector_size < 0)
      return {};

    vector_exprt value({}, vector_type);
    value.operands().resize(numeric_cast_v<std::size_t>(vector_size), *tmpval);
    value.add_source_location()=source_location;

    return std::move(value);
  }
  else if(type_id==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    struct_exprt value({}, type);

    value.operands().reserve(components.size());

    for(const auto &c : components)
    {
      DATA_INVARIANT(
        c.type().id() != ID_code, "struct member must not be of code type");

      const auto member =
        expr_initializer_rec(c.type(), source_location, init_expr);
      if(!member.has_value())
        return {};

      value.add_to_operands(std::move(*member));
    }

    value.add_source_location()=source_location;

    return std::move(value);
  }
  else if(type_id==ID_union)
  {
    const union_typet &union_type = to_union_type(type);

    if(union_type.components().empty())
    {
      empty_union_exprt value{type};
      value.add_source_location() = source_location;
      return std::move(value);
    }

    const auto &widest_member = union_type.find_widest_union_component(ns);
    if(!widest_member.has_value())
      return {};

    auto component_value = expr_initializer_rec(
      widest_member->first.type(), source_location, init_expr);

    if(!component_value.has_value())
      return {};

    union_exprt value{widest_member->first.get_name(), *component_value, type};
    value.add_source_location() = source_location;

    return std::move(value);
  }
  else if(type_id==ID_c_enum_tag)
  {
    auto result = expr_initializer_rec(
      ns.follow_tag(to_c_enum_tag_type(type)), source_location, init_expr);

    if(!result.has_value())
      return {};

    // use the tag type
    result->type() = type;

    return *result;
  }
  else if(type_id==ID_struct_tag)
  {
    auto result = expr_initializer_rec(
      ns.follow_tag(to_struct_tag_type(type)), source_location, init_expr);

    if(!result.has_value())
      return {};

    // use the tag type
    result->type() = type;

    return *result;
  }
  else if(type_id==ID_union_tag)
  {
    auto result = expr_initializer_rec(
      ns.follow_tag(to_union_tag_type(type)), source_location, init_expr);

    if(!result.has_value())
      return {};

    // use the tag type
    result->type() = type;

    return *result;
  }
  else if(type_id==ID_string)
  {
    exprt result;
    if(init_expr.id() == ID_nondet)
      result = side_effect_expr_nondett(type, source_location);
    else if(init_expr.is_zero())
      result = constant_exprt(irep_idt(), type);
    else
      result = duplicate_per_byte(init_expr, type, ns);

    result.add_source_location()=source_location;
    return result;
  }
  else
    return {};
}

/// Create the equivalent of zero for type `type`.
/// \param type: Type of the target expression.
/// \param source_location: Location to record in all created sub-expressions.
/// \param ns: Namespace to perform type symbol/tag lookups.
/// \return An expression if a constant expression of the input type can be
///   built.
std::optional<exprt> zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  return expr_initializert(ns)(
    type, source_location, constant_exprt(ID_0, char_type()));
}

/// Create a non-deterministic value for type `type`, with all subtypes
/// independently expanded as non-deterministic values.
/// \param type: Type of the target expression.
/// \param source_location: Location to record in all created sub-expressions.
/// \param ns: Namespace to perform type symbol/tag lookups.
/// \return An expression if a non-deterministic expression of the input type
///   can be built.
std::optional<exprt> nondet_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  return expr_initializert(ns)(type, source_location, exprt(ID_nondet));
}

/// Create a value for type `type`, with all subtype bytes
/// initialized to the given value.
/// \param type: Type of the target expression.
/// \param source_location: Location to record in all created sub-expressions.
/// \param ns: Namespace to perform type symbol/tag lookups.
/// \param init_byte_expr: Value to be used for initialization.
/// \return An expression if a byte-initialized expression of the input type
///   can be built.
std::optional<exprt> expr_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns,
  const exprt &init_byte_expr)
{
  return expr_initializert(ns)(type, source_location, init_byte_expr);
}

/// Typecast the input to the output if this is a signed/unsigned bv.
/// Perform a reinterpret cast using byte_extract otherwise.
/// @param expr the expression to be casted if necessary.
/// @param out_type the type to cast the expression to.
/// @return the casted or reinterpreted expression.
static exprt cast_or_reinterpret(const exprt &expr, const typet &out_type)
{
  // Same type --> no cast
  if(expr.type() == out_type)
  {
    return expr;
  }
  if(
    can_cast_type<signedbv_typet>(out_type) ||
    can_cast_type<unsignedbv_typet>(out_type))
  {
    return typecast_exprt::conditional_cast(expr, out_type);
  }
  return make_byte_extract(expr, from_integer(0, char_type()), out_type);
}

/// Builds an expression of the given output type with each of its bytes
/// initialized to the given initialization expression.
/// Integer bitvector types are currently supported.
/// For unsupported `output_type` the initialization expression is casted to the
/// output type.
/// \param init_byte_expr The initialization expression
/// \param output_type The output type
/// \param ns Namespace to perform type symbol/tag lookups
/// \return The built expression
/// \note `init_byte_expr` must be a boolean or a bitvector and must be of at
///  most `size <= config.ansi_c.char_width`
exprt duplicate_per_byte(
  const exprt &init_byte_expr,
  const typet &output_type,
  const namespacet &ns)
{
  const auto init_type_as_bitvector =
    type_try_dynamic_cast<bitvector_typet>(init_byte_expr.type());
  // Fail if `init_byte_expr` is not a bitvector of maximum 8 bits or a boolean.
  PRECONDITION(
    (init_type_as_bitvector &&
     init_type_as_bitvector->get_width() <= config.ansi_c.char_width) ||
    init_byte_expr.type().id() == ID_bool);
  // Simplify init_expr to enable faster duplication when simplifiable to a
  // constant expr
  const auto simplified_init_expr = simplify_expr(init_byte_expr, ns);
  if(const auto output_bv = type_try_dynamic_cast<bitvector_typet>(output_type))
  {
    const auto out_width = output_bv->get_width();
    // Replicate `simplified_init_expr` enough times until it completely fills
    // `output_type`.

    // We've got a constant. So, precompute the value of the constant.
    if(simplified_init_expr.is_constant())
    {
      const auto init_size = init_type_as_bitvector->get_width();
      const irep_idt init_value =
        to_constant_expr(simplified_init_expr).get_value();

      // Create a new BV of `output_type` size with its representation being the
      // replication of the simplified_init_expr (padded with 0) enough times to
      // fill.
      const auto output_value =
        make_bvrep(out_width, [&init_size, &init_value](std::size_t index) {
          // Index modded by 8 to access the i-th bit of init_value
          const auto source_index = index % config.ansi_c.char_width;
          // If the modded i-th bit exists get it, otherwise add 0 padding.
          return source_index < init_size &&
                 get_bvrep_bit(init_value, init_size, source_index);
        });

      return constant_exprt{output_value, output_type};
    }

    const size_t size =
      (out_width + config.ansi_c.char_width - 1) / config.ansi_c.char_width;

    // We haven't got a constant. So, build the expression using shift-and-or.
    exprt::operandst values;

    // When doing the replication we extend the init_expr to the output size to
    // compute the bitwise or. To avoid that the sign is extended too we change
    // the type of the output to an unsigned bitvector with the same size as the
    // output type.
    typet operation_type = unsignedbv_typet{output_bv->get_width()};
    // To avoid sign-extension during cast we first cast to an unsigned version
    // of the same bv type, then we extend it to the output type (adding 0
    // padding).
    const exprt casted_init_byte_expr = typecast_exprt::conditional_cast(
      typecast_exprt::conditional_cast(
        init_byte_expr, unsignedbv_typet{init_type_as_bitvector->get_width()}),
      operation_type);

    values.push_back(casted_init_byte_expr);
    for(size_t i = 1; i < size; ++i)
    {
      values.push_back(shl_exprt(
        casted_init_byte_expr,
        from_integer(config.ansi_c.char_width * i, size_type())));
    }
    return cast_or_reinterpret(
      values.size() == 1 ? values[0]
                         : multi_ary_exprt(ID_bitor, values, operation_type),
      output_type);
  }

  // Anything else. We don't know what to do with it. So, just cast.
  return typecast_exprt::conditional_cast(init_byte_expr, output_type);
}
