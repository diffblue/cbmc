/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <message_stream.h>
#include <arith_tools.h>
#include <expr_util.h>
#include <std_types.h>
#include <std_expr.h>

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
    const locationt &location)
  {
    return zero_initializer_rec(type, location);
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
    const locationt &location);
};

/*******************************************************************\

Function: zero_initializert::zero_initializer_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt zero_initializert::zero_initializer_rec(
  const typet &type,
  const locationt &location)
{
  const irep_idt &type_id=type.id();
  
  if(type_id==ID_bool)
  {
    exprt result=false_exprt();
    result.location()=location;
    return result;
  }
  else if(type_id==ID_unsignedbv ||
          type_id==ID_signedbv ||
          type_id==ID_floatbv ||
          type_id==ID_fixedbv ||
          type_id==ID_pointer ||
          type_id==ID_complex)
  {
    exprt result=gen_zero(type);
    result.location()=location;
    return result;
  }
  else if(type_id==ID_code)
  {
    err_location(location);
    error("cannot zero-initialize code-type");
    throw 0;
  }
  else if(type_id==ID_c_enum ||
          type_id==ID_incomplete_c_enum)
  {
    constant_exprt value(type);
    value.set_value(ID_0);
    value.location()=location;
    return value;
  }
  else if(type_id==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    
    if(array_type.size().is_nil())
    {
      // we initialize this with an empty array

      array_exprt value(type);
      value.type().id(ID_array);
      value.type().set(ID_size, gen_zero(size_type()));
      value.location()=location;
      return value;
    }
    else
    {
      exprt tmpval=zero_initializer_rec(array_type.subtype(), location);

      mp_integer array_size;

      if(array_type.size().id()==ID_infinity)
      {
        exprt value(ID_array_of, type);
        value.copy_to_operands(tmpval);
        value.location()=location;
        return value;
      }
      else if(to_integer(array_type.size(), array_size))
      {
        err_location(location);
        str << "failed to zero-initialize array of non-fixed size `"
            << to_string(array_type.size()) << "'";
        error();
        throw 0;
      }
        
      if(array_size<0)
      {
        err_location(location);
        error("failed to zero-initialize array of with negative size");
        throw 0;
      }

      array_exprt value(type);
      value.operands().resize(integer2long(array_size), tmpval);
      value.location()=location;
      return value;
    }
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);
    
    exprt tmpval=zero_initializer_rec(vector_type.subtype(), location);

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      err_location(location);
      str << "failed to zero-initialize vector of non-fixed size `"
          << to_string(vector_type.size()) << "'";
      error();
      throw 0;
    }
      
    if(vector_size<0)
    {
      err_location(location);
      error("failed to zero-initialize vector of with negative size");
      throw 0;
    }

    vector_exprt value(vector_type);
    value.operands().resize(integer2long(vector_size), tmpval);
    value.location()=location;

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
      value.copy_to_operands(zero_initializer_rec(it->type(), location));

    value.location()=location;

    return value;
  }
  else if(type_id==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    exprt value(ID_union, type);

    if(components.empty())
      return value; // stupid empty union

    value.set(ID_component_name, components.front().get(ID_name));
    value.copy_to_operands(
      zero_initializer_rec(components.front().type(), location));
    value.location()=location;

    return value;
  }
  else if(type_id==ID_symbol)
  {
    return zero_initializer_rec(ns.follow(type), location);
  }
  else
  {
    err_location(location);
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
  const locationt &location,
  const namespacet &ns,
  message_handlert &message_handler)
{
  zero_initializert z_i(ns, message_handler);
  return z_i(type, location);
}
