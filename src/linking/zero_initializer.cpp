/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/message_stream.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>

#include <ansi-c/c_types.h>
#include <ansi-c/expr2c.h>

#include "zero_initializer.h"

class zero_initializert:public message_streamt
{
public:
  zero_initializert(
    const namespacet &_ns,
    message_handlert &_message_handler):
    message_streamt(_message_handler),
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

/*******************************************************************\

Function: zero_initializert::zero_initializer_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt zero_initializert::zero_initializer_rec(
  const typet &type,
  const source_locationt &source_location)
{
  const irep_idt &type_id=type.id();
  
  if(type_id==ID_bool)
  {
    exprt result=false_exprt();
    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_unsignedbv ||
          type_id==ID_signedbv ||
          type_id==ID_floatbv ||
          type_id==ID_fixedbv ||
          type_id==ID_pointer ||
          type_id==ID_complex ||
          type_id==ID_c_enum ||
          type_id==ID_incomplete_c_enum ||
          type_id==ID_c_enum_tag ||
          type_id==ID_c_bit_field ||
          type_id==ID_c_bool)
  {
    exprt result=gen_zero(type);
    result.add_source_location()=source_location;
    return result;
  }
  else if(type_id==ID_code)
  {
    err_location(source_location);
    error("cannot zero-initialize code-type");
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
      value.type().set(ID_size, gen_zero(size_type()));
      value.add_source_location()=source_location;
      return value;
    }
    else
    {
      exprt tmpval=zero_initializer_rec(array_type.subtype(), source_location);

      mp_integer array_size;

      if(array_type.size().id()==ID_infinity)
      {
        exprt value(ID_array_of, type);
        value.copy_to_operands(tmpval);
        value.add_source_location()=source_location;
        return value;
      }
      else if(to_integer(array_type.size(), array_size))
      {
        err_location(source_location);
        str << "failed to zero-initialize array of non-fixed size `"
            << to_string(array_type.size()) << "'";
        error();
        throw 0;
      }
        
      if(array_size<0)
      {
        err_location(source_location);
        error("failed to zero-initialize array of with negative size");
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
      err_location(source_location);
      str << "failed to zero-initialize vector of non-fixed size `"
          << to_string(vector_type.size()) << "'";
      error();
      throw 0;
    }
      
    if(vector_size<0)
    {
      err_location(source_location);
      error("failed to zero-initialize vector of with negative size");
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

    exprt value(ID_struct, type);
    
    value.operands().reserve(components.size());

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->type().id()==ID_code)
      {
        constant_exprt code_value(it->type());
        code_value.set_value(ID_nil);
        code_value.add_source_location()=source_location;
        value.copy_to_operands(code_value);
      }
      else
        value.copy_to_operands(zero_initializer_rec(it->type(), source_location));
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
      if(it->type().id()==ID_code) continue;

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
  else
  {
    err_location(source_location);
    str << "failed to zero-initialize `" << to_string(type)
        << "'";
    error();
    throw 0;
  }
}

/*******************************************************************\

Function: zero_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns,
  message_handlert &message_handler)
{
  zero_initializert z_i(ns, message_handler);
  return z_i(type, source_location);
}
