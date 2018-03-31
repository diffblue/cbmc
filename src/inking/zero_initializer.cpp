/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Linking: Zero Initialization

#include "zero_initializer.h"

#include <sstream>

#include <util/namespace.h>
#include <util/message.h>
#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>

#include <util/c_types.h>
#include <ansi-c/expr2c.h>

class zero_initializert:public messaget
{
public:
  zero_initializert(
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
    return zero_initializer_rec(type, source_location);
  }

protected:
  const namespacet &ns;

  std::string to_string(const exprt &src)
  {
    return expr2c(src, ns);
  }

  std::string to_string(const typet &src)
  {
    return type2c(src, ns);
  }

  exprt zero_initializer_rec(
    const typet &type,
    const source_locationt &source_location);
};

exprt zero_initializert::zero_initializer_rec(
  const typet &type,
  const source_locationt &source_location)
{
  const irep_idt &type_id=type.id();

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
    exprt result=from_integer(0, type);
    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_rational ||
          type_id==ID_real)
  {
    constant_exprt result(ID_0, type);
    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_verilog_signedbv ||
          type_id==ID_verilog_unsignedbv)
  {
    std::size_t width=to_bitvector_type(type).get_width();
    std::string value(width, '0');

    constant_exprt result(value, type);
    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_complex)
  {
    exprt sub_zero=zero_initializer_rec(type.subtype(), source_location);
    complex_exprt result(sub_zero, sub_zero, to_complex_type(type));
    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_code)
  {
    error().source_location=source_location;
    error() << "cannot zero-initialize code-type" << eom;
    throw 0;
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
      return value;
    }
    else
    {
      exprt tmpval=zero_initializer_rec(array_type.subtype(), source_location);

      mp_integer array_size;

      if(array_type.size().id()==ID_infinity)
      {
        array_of_exprt value(tmpval, array_type);
        value.add_source_location()=source_location;
        return value;
      }
      else if(to_integer(array_type.size(), array_size))
      {
        error().source_location=source_location;
        error() << "failed to zero-initialize array of non-fixed size `"
                << to_string(array_type.size()) << "'" << eom;
        throw 0;
      }

      if(array_size<0)
      {
        error().source_location=source_location;
        error() << "failed to zero-initialize array of with negative size"
                << eom;
        throw 0;
      }

      array_exprt value(array_type);
      value.operands().resize(integer2unsigned(array_size), tmpval);
      value.add_source_location()=source_location;
      return value;
    }
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);

    exprt tmpval=zero_initializer_rec(vector_type.subtype(), source_location);

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      error().source_location=source_location;
      error() << "failed to zero-initialize vector of non-fixed size `"
              << to_string(vector_type.size()) << "'" << eom;
      throw 0;
    }

    if(vector_size<0)
    {
      error().source_location=source_location;
      error() << "failed to zero-initialize vector of with negative size"
              << eom;
      throw 0;
    }

    vector_exprt value(vector_type);
    value.operands().resize(integer2unsigned(vector_size), tmpval);
    value.add_source_location()=source_location;

    return value;
  }
  else if(type_id==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    struct_exprt value(type);

    value.operands().reserve(components.size());

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->type().id()==ID_code)
      {
        constant_exprt code_value(ID_nil, it->type());
        code_value.add_source_location()=source_location;
        value.copy_to_operands(code_value);
      }
      else
        value.copy_to_operands(
          zero_initializer_rec(it->type(), source_location));
    }

    value.add_source_location()=source_location;

    return value;
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

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      // skip methods
      if(it->type().id()==ID_code)
        continue;

      mp_integer bits=pointer_offset_bits(it->type(), ns);

      if(bits>component_size)
      {
        component=*it;
        found=true;
        component_size=bits;
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
        zero_initializer_rec(component.type(), source_location);
    }

    return value;
  }
  else if(type_id==ID_symbol)
  {
    exprt result=zero_initializer_rec(ns.follow(type), source_location);
    // we might have mangled the type for arrays, so keep that
    if(ns.follow(type).id()!=ID_array)
      result.type()=type;

    return result;
  }
  else if(type_id==ID_c_enum_tag)
  {
    return
      zero_initializer_rec(
        ns.follow_tag(to_c_enum_tag_type(type)),
        source_location);
  }
  else if(type_id==ID_struct_tag)
  {
    return
      zero_initializer_rec(
        ns.follow_tag(to_struct_tag_type(type)),
        source_location);
  }
  else if(type_id==ID_union_tag)
  {
    return
      zero_initializer_rec(
        ns.follow_tag(to_union_tag_type(type)),
        source_location);
  }
  else if(type_id==ID_string)
  {
    return constant_exprt(irep_idt(), type);
  }
  else
  {
    error().source_location=source_location;
    error() << "failed to zero-initialize `" << to_string(type)
            << "'" << eom;
    throw 0;
  }
}

exprt zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns,
  message_handlert &message_handler)
{
  zero_initializert z_i(ns, message_handler);
  return z_i(type, source_location);
}

exprt zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns)
{
  std::ostringstream oss;
  stream_message_handlert mh(oss);

  try
  {
    zero_initializert z_i(ns, mh);
    return z_i(type, source_location);
  }
  catch(int)
  {
    throw oss.str();
  }
}
