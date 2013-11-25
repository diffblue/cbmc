/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "expr.h"
#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"
#include "expr_util.h"
#include "config.h"
#include "simplify_expr.h"
#include "namespace.h"
#include "symbol.h"

#include "pointer_offset_size.h"

/*******************************************************************\

Function: member_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer member_offset(
  const namespacet &ns,
  const struct_typet &type,
  const irep_idt &member)
{
  const struct_typet::componentst &components=type.components();
  
  mp_integer result=0;
  unsigned bit_field_bits=0;
  
  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    if(it->get_name()==member)
      break;

    if(it->get_is_bit_field())
    {
      // take the extra bytes needed
      unsigned w=it->type().get_int(ID_width);
      for(; w>bit_field_bits; ++result, bit_field_bits+=8);
      bit_field_bits-=w;
    }
    else
    {
      const typet &subtype=it->type();
      mp_integer sub_size=pointer_offset_size(ns, subtype);
      if(sub_size==-1) return -1; // give up
      result+=sub_size;
    }
  }

  return result;
}

/*******************************************************************\

Function: pointer_offset_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer pointer_offset_size(
  const namespacet &ns,
  const typet &type)
{
  if(type.id()==ID_array)
  {
    mp_integer sub=pointer_offset_size(ns, type.subtype());
  
    // get size
    const exprt &size=to_array_type(type).size();

    // constant?
    mp_integer i;
    
    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements
    
    return sub*i;
  }
  else if(type.id()==ID_vector)
  {
    mp_integer sub=pointer_offset_size(ns, type.subtype());
  
    // get size
    const exprt &size=to_vector_type(type).size();

    // constant?
    mp_integer i;
    
    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements
    
    return sub*i;
  }
  else if(type.id()==ID_complex)
  {
    mp_integer sub=pointer_offset_size(ns, type.subtype());
    return sub*2;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();
      
    mp_integer result=0;
    unsigned bit_field_bits=0;
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_is_bit_field())
      {
        unsigned w=it->type().get_int(ID_width);
        for(; w>bit_field_bits; ++result, bit_field_bits+=8);
        bit_field_bits-=w;
      }
      else
      {
        const typet &subtype=it->type();
        mp_integer sub_size=pointer_offset_size(ns, subtype);
        if(sub_size==-1) return -1;
        result+=sub_size;
      }
    }

    return result;
  }
  else if(type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(type);
    const union_typet::componentst &components=
      union_type.components();
      
    mp_integer result=0;

    // compute max
    
    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      mp_integer sub_size=pointer_offset_size(ns, subtype);
      if(sub_size>result) result=sub_size;
    }
    
    return result;
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_enum)
  {
    unsigned width=to_bitvector_type(type).get_width();
    unsigned bytes=width/8;
    if(bytes*8!=width) bytes++;
    return bytes;
  }
  else if(type.id()==ID_bool)
    return 1;
  else if(type.id()==ID_pointer)
  {
    unsigned width=config.ansi_c.pointer_width;
    unsigned bytes=width/8;
    if(bytes*8!=width) bytes++;
    return bytes;
  }
  else if(type.id()==ID_symbol)
    return pointer_offset_size(ns, ns.follow(type));
  else if(type.id()==ID_code)
    return 0;
  else
    return mp_integer(-1);
}

/*******************************************************************\

Function: member_offset_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  const struct_typet::componentst &components=type.components();
  
  exprt result=gen_zero(signedbv_typet(config.ansi_c.pointer_width));
  unsigned bit_field_bits=0;
  
  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    if(it->get_name()==member) break;

    if(it->get_is_bit_field())
    {
      unsigned w=it->type().get_int(ID_width);
      unsigned bytes;
      for(bytes=0; w>bit_field_bits; ++bytes, bit_field_bits+=8);
      bit_field_bits-=w;
      result=plus_exprt(result, from_integer(bytes, result.type()));
    }
    else
    {
      const typet &subtype=it->type();
      exprt sub_size=size_of_expr(subtype, ns);
      if(sub_size.is_nil()) return nil_exprt(); // give up
      result=plus_exprt(result, sub_size);
    }
  }

  simplify(result, ns);
  
  return result;
}

/*******************************************************************\

Function: size_of_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt size_of_expr(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil()) return nil_exprt();
  
    // get size
    exprt size=to_array_type(type).size();
    
    if(size.is_nil()) return nil_exprt();
    
    if(size.type()!=sub.type())
      size.make_typecast(sub.type());
    
    exprt result=mult_exprt(size, sub);

    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_vector)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil()) return nil_exprt();
  
    // get size
    exprt size=to_vector_type(type).size();
    
    if(size.is_nil()) return nil_exprt();
    
    if(size.type()!=sub.type())
      size.make_typecast(sub.type());
    
    exprt result=mult_exprt(size, sub);
    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_complex)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil()) return nil_exprt();
  
    const exprt size=from_integer(2, sub.type());
    
    exprt result=mult_exprt(size, sub);
    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();
      
    exprt result=gen_zero(signedbv_typet(config.ansi_c.pointer_width));
    unsigned bit_field_bits=0;
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_is_bit_field())
      {
        unsigned w=it->type().get_int(ID_width);
        unsigned bytes;
        for(bytes=0; w>bit_field_bits; ++bytes, bit_field_bits+=8);
        bit_field_bits-=w;
        result=plus_exprt(result, from_integer(bytes, result.type()));
      }
      else
      {
        const typet &subtype=it->type();
        exprt sub_size=size_of_expr(subtype, ns);
        if(sub_size.is_nil()) return nil_exprt();

        result=plus_exprt(result, sub_size);
      }
    }

    simplify(result, ns);
    
    return result;
  }
  else if(type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(type);
    const union_typet::componentst &components=
      union_type.components();
      
    mp_integer result=0;

    // compute max
    
    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      mp_integer sub_size=pointer_offset_size(ns, subtype);
      if(sub_size>result) result=sub_size;
    }
    
    return from_integer(result, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_enum)
  {
    unsigned width=to_bitvector_type(type).get_width();
    unsigned bytes=width/8;
    if(bytes*8!=width) bytes++;
    return from_integer(bytes, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_bool)
  {
    return gen_one(signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_pointer)
  {
    unsigned width=config.ansi_c.pointer_width;
    unsigned bytes=width/8;
    if(bytes*8!=width) bytes++;
    return from_integer(bytes, signedbv_typet(config.ansi_c.pointer_width));
  }
  else if(type.id()==ID_symbol)
  {
    return size_of_expr(ns.follow(type), ns);
  }
  else if(type.id()==ID_code)
  {
    return gen_zero(signedbv_typet(config.ansi_c.pointer_width));
  }
  else
    return nil_exprt();
}

/*******************************************************************\

Function: compute_pointer_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer compute_pointer_offset(
  const namespacet &ns,
  const exprt &expr)
{
  if(expr.id()==ID_symbol)
    return 0;
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    
    const typet &array_type=ns.follow(expr.op0().type());
    assert(array_type.id()==ID_array);

    mp_integer o=compute_pointer_offset(ns, expr.op0());
    
    if(o!=-1)
    {
      mp_integer sub_size=
        pointer_offset_size(ns, array_type.subtype());

      mp_integer i;

      if(sub_size!=0 && !to_integer(expr.op1(), i))
        return o+i*sub_size;
    }
      
    // don't know
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    const typet &type=ns.follow(expr.op0().type());
    
    assert(type.id()==ID_struct ||
           type.id()==ID_union);

    mp_integer o=compute_pointer_offset(ns, expr.op0());

    if(o!=-1)
    {    
      if(type.id()==ID_union)
        return o;
    
      return o+member_offset(
        ns, to_struct_type(type), expr.get(ID_component_name));
    }
  }
  else if(expr.id()==ID_string_constant)
    return 0;

  return -1; // don't know
}
