/*******************************************************************\

Module: Expression Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Initialization

#include "expr_initializer.h"

#include "arith_tools.h"
#include "c_types.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "std_code.h"
#include "std_expr.h"

template <bool nondet>
class expr_initializert
{
public:
  explicit expr_initializert(const namespacet &_ns) : ns(_ns)
  {
  }

  exprt operator()(
    const typet &type,
    const source_locationt &source_location)
  {
    return expr_initializer_rec(type, source_location);
  }

protected:
  const namespacet &ns;

  exprt expr_initializer_rec(
    const typet &type,
    const source_locationt &source_location);
};

template <bool nondet>
exprt expr_initializert<nondet>::expr_initializer_rec(
  const typet &type,
  const source_locationt &source_location)
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
    if(nondet)
      result = side_effect_expr_nondett(type, source_location);
    else
      result = from_integer(0, type);

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_rational ||
          type_id==ID_real)
  {
    exprt result;
    if(nondet)
      result = side_effect_expr_nondett(type, source_location);
    else
      result = constant_exprt(ID_0, type);

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_verilog_signedbv ||
          type_id==ID_verilog_unsignedbv)
  {
    exprt result;
    if(nondet)
      result = side_effect_expr_nondett(type, source_location);
    else
    {
      const std::size_t width = to_bitvector_type(type).get_width();
      std::string value(width, '0');

      result = constant_exprt(value, type);
    }

    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_complex)
  {
    exprt result;
    if(nondet)
      result = side_effect_expr_nondett(type, source_location);
    else
    {
      exprt sub_zero =
        expr_initializer_rec(to_complex_type(type).subtype(), source_location);
      if(sub_zero.is_nil())
        return nil_exprt();

      result = complex_exprt(sub_zero, sub_zero, to_complex_type(type));
    }

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
      value.type().id(ID_array);
      value.type().set(ID_size, from_integer(0, size_type()));
      value.add_source_location()=source_location;
      return std::move(value);
    }
    else
    {
      exprt tmpval =
        expr_initializer_rec(array_type.subtype(), source_location);
      if(tmpval.is_nil())
        return nil_exprt();

      if(array_type.size().id()==ID_infinity)
      {
        if(nondet)
          return side_effect_expr_nondett(type, source_location);

        array_of_exprt value(tmpval, array_type);
        value.add_source_location()=source_location;
        return std::move(value);
      }

      const auto array_size = numeric_cast<mp_integer>(array_type.size());
      if(!array_size.has_value())
      {
        if(nondet)
          return side_effect_expr_nondett(type, source_location);
        else
          return nil_exprt();
      }

      if(*array_size < 0)
        return nil_exprt();

      array_exprt value({}, array_type);
      value.operands().resize(numeric_cast_v<std::size_t>(*array_size), tmpval);
      value.add_source_location()=source_location;
      return std::move(value);
    }
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);

    exprt tmpval = expr_initializer_rec(vector_type.subtype(), source_location);
    if(tmpval.is_nil())
      return nil_exprt();

    const mp_integer vector_size =
      numeric_cast_v<mp_integer>(vector_type.size());

    if(vector_size < 0)
      return nil_exprt();

    vector_exprt value({}, vector_type);
    value.operands().resize(numeric_cast_v<std::size_t>(vector_size), tmpval);
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
      if(c.type().id() == ID_code)
      {
        constant_exprt code_value(ID_nil, c.type());
        code_value.add_source_location()=source_location;
        value.add_to_operands(std::move(code_value));
      }
      else
      {
        const exprt member = expr_initializer_rec(c.type(), source_location);
        if(member.is_nil())
          return nil_exprt();

        value.add_to_operands(std::move(member));
      }
    }

    value.add_source_location()=source_location;

    return std::move(value);
  }
  else if(type_id==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    union_typet::componentt component;
    bool found=false;
    mp_integer component_size=0;

    // we need to find the largest member

    for(const auto &c : components)
    {
      // skip methods
      if(c.type().id() == ID_code)
        continue;

      auto bits = pointer_offset_bits(c.type(), ns);

      if(bits.has_value() && *bits > component_size)
      {
        component = c;
        found=true;
        component_size = *bits;
      }
    }

    union_exprt value("", nil_exprt(), type);
    value.add_source_location()=source_location;

    if(!found)
    {
      // stupid empty union
    }
    else
    {
      value.set_component_name(component.get_name());
      value.op()=
        expr_initializer_rec(component.type(), source_location);
      if(value.op().is_nil())
        return nil_exprt();
    }

    return std::move(value);
  }
  else if(type_id == ID_symbol_type)
  {
    exprt result = expr_initializer_rec(ns.follow(type), source_location);
    // we might have mangled the type for arrays, so keep that
    if(type.id() != ID_array)
      result.type()=type;

    return result;
  }
  else if(type_id==ID_c_enum_tag)
  {
    exprt result = expr_initializer_rec(
      ns.follow_tag(to_c_enum_tag_type(type)), source_location);

    // use the tag type
    result.type() = type;

    return result;
  }
  else if(type_id==ID_struct_tag)
  {
    exprt result = expr_initializer_rec(
      ns.follow_tag(to_struct_tag_type(type)), source_location);

    // use the tag type
    result.type() = type;

    return result;
  }
  else if(type_id==ID_union_tag)
  {
    exprt result = expr_initializer_rec(
      ns.follow_tag(to_union_tag_type(type)), source_location);

    // use the tag type
    result.type() = type;

    return result;
  }
  else if(type_id==ID_string)
  {
    exprt result;
    if(nondet)
      result = side_effect_expr_nondett(type, source_location);
    else
      result = constant_exprt(irep_idt(), type);

    result.add_source_location()=source_location;
    return result;
  }
  else
    return nil_exprt();
}

/// Create the equivalent of zero for type `type`.
/// \param type: Type of the target expression.
/// \param source_location: Location to record in all created sub-expressions.
/// \param ns: Namespace to perform type symbol/tag lookups.
/// \return An expression if a constant expression of the input type can be
///   built.
optionalt<exprt> zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  expr_initializert<false> z_i(ns);
  const exprt result = z_i(type, source_location);
  if(result.is_nil())
    return {};
  else
    return result;
}

/// Create a non-deterministic value for type `type`, with all subtypes
/// independently expanded as non-deterministic values.
/// \param type: Type of the target expression.
/// \param source_location: Location to record in all created sub-expressions.
/// \param ns: Namespace to perform type symbol/tag lookups.
/// \return An expression if a non-deterministic expression of the input type
///   can be built.
optionalt<exprt> nondet_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  expr_initializert<true> z_i(ns);
  const exprt result = z_i(type, source_location);
  if(result.is_nil())
    return {};
  else
    return result;
}
