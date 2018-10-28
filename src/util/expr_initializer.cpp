/*******************************************************************\

Module: Expression Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Initialization

#include "expr_initializer.h"

#include "arith_tools.h"
#include "c_types.h"
#include "format_expr.h"
#include "format_type.h"
#include "invariant.h"
#include "message.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "std_code.h"
#include "std_expr.h"

template <bool nondet>
class expr_initializert : public messaget
{
public:
  expr_initializert(
    const namespacet &_ns,
    message_handlert &_message_handler):
    messaget(_message_handler),
    ns(_ns)
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

  PRECONDITION_WITH_DIAGNOSTICS(
    type_id != ID_code,
    source_location.as_string() + ": cannot initialize code type");

  if(type_id==ID_unsignedbv ||
     type_id==ID_signedbv ||
     type_id==ID_pointer ||
     type_id==ID_c_enum ||
     type_id==ID_incomplete_c_enum ||
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

      array_exprt value(array_type);
      value.type().id(ID_array);
      value.type().set(ID_size, from_integer(0, size_type()));
      value.add_source_location()=source_location;
      return std::move(value);
    }
    else
    {
      exprt tmpval =
        expr_initializer_rec(array_type.subtype(), source_location);

      mp_integer array_size;

      if(array_type.size().id()==ID_infinity)
      {
        if(nondet)
          return side_effect_expr_nondett(type, source_location);

        array_of_exprt value(tmpval, array_type);
        value.add_source_location()=source_location;
        return std::move(value);
      }
      else if(to_integer(array_type.size(), array_size))
      {
        if(nondet)
          return side_effect_expr_nondett(type, source_location);

        std::ostringstream oss;
        oss << format(array_type.size());

        INVARIANT_WITH_DIAGNOSTICS(
          false,
          "non-infinite array size expression must be convertible to an "
          "integer",
          source_location.as_string() +
            ": failed to zero-initialize array of size `" + oss.str() + "'");
      }

      DATA_INVARIANT(
        array_size >= 0, "array should not have negative size");

      array_exprt value(array_type);
      value.operands().resize(integer2size_t(array_size), tmpval);
      value.add_source_location()=source_location;
      return std::move(value);
    }
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);

    exprt tmpval = expr_initializer_rec(vector_type.subtype(), source_location);

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      if(nondet)
        return side_effect_expr_nondett(type, source_location);

      std::ostringstream oss;
      oss << format(vector_type.size());

      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "vector size must be convertible to an integer",
        source_location.as_string() +
          ": failed to zero-initialize vector of size `" + oss.str() + "'");
    }

    DATA_INVARIANT(
      vector_size >= 0, "vector should not have negative size");

    vector_exprt value(vector_type);
    value.operands().resize(integer2size_t(vector_size), tmpval);
    value.add_source_location()=source_location;

    return std::move(value);
  }
  else if(type_id==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    struct_exprt value(type);

    value.operands().reserve(components.size());

    for(const auto &c : components)
    {
      if(c.type().id() == ID_code)
      {
        constant_exprt code_value(ID_nil, c.type());
        code_value.add_source_location()=source_location;
        value.copy_to_operands(code_value);
      }
      else
        value.copy_to_operands(expr_initializer_rec(c.type(), source_location));
    }

    value.add_source_location()=source_location;

    return std::move(value);
  }
  else if(type_id==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    union_exprt value(type);

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

    value.add_source_location()=source_location;

    if(!found)
    {
      // stupid empty union
      value.op()=nil_exprt();
    }
    else
    {
      value.set_component_name(component.get_name());
      value.op()=
        expr_initializer_rec(component.type(), source_location);
    }

    return std::move(value);
  }
  else if(type_id == ID_symbol_type)
  {
    exprt result = expr_initializer_rec(ns.follow(type), source_location);
    // we might have mangled the type for arrays, so keep that
    if(ns.follow(type).id()!=ID_array)
      result.type()=type;

    return result;
  }
  else if(type_id==ID_c_enum_tag)
  {
    return
      expr_initializer_rec(
        ns.follow_tag(to_c_enum_tag_type(type)),
        source_location);
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
  {
    std::ostringstream oss;
    oss << format(type);

    PRECONDITION_WITH_DIAGNOSTICS(
      false,
      source_location.as_string() + ": cannot initialize " + oss.str() + "'");
  }
}

exprt zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr_initializert<false> z_i(ns, message_handler);
  return z_i(type, source_location);
}

exprt nondet_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr_initializert<true> z_i(ns, message_handler);
  return z_i(type, source_location);
}

exprt zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  null_message_handlert null_message_handler;
  expr_initializert<false> z_i(ns, null_message_handler);
  return z_i(type, source_location);
}

exprt nondet_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  null_message_handlert null_message_handler;
  expr_initializert<true> z_i(ns, null_message_handler);
  return z_i(type, source_location);
}
