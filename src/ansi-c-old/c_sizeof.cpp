/*******************************************************************\

Module: Conversion of sizeof Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/config.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "c_sizeof.h"
#include "c_typecast.h"
#include "c_types.h"

/*******************************************************************\

Function: c_sizeoft::sizeof_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_sizeoft::sizeof_rec(const typet &type)
{
  // this implementation will eventually be replaced
  // by size_of_expr in util/pointer_offset_size.h
  exprt dest;
  
  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv ||
     type.id()==ID_c_enum ||
     type.id()==ID_incomplete_c_enum)
  {
    // We round up to bytes.
    // See special treatment for bit-fields below.
    unsigned bits=type.get_int(ID_width);
    unsigned bytes=bits/8;
    if((bits%8)!=0) bytes++;
    dest=from_integer(bytes, size_type());
  }
  else if(type.id()==ID_pointer)
  {
    // the following is an MS extension
    if(type.get_bool(ID_C_ptr32))
      return from_integer(4, size_type());
             
    unsigned bits=config.ansi_c.pointer_width;
    unsigned bytes=bits/8;
    if((bits%8)!=0) bytes++;
    dest=from_integer(bytes, size_type());
  }
  else if(type.id()==ID_bool)
  {
    // We fit booleans into a byte.
    dest=from_integer(1, size_type());
  }
  else if(type.id()==ID_array)
  {
    const exprt &size_expr=
      to_array_type(type).size();
      
    if(size_expr.is_nil())
    {
      // treated like an empty array
      dest=from_integer(0, size_type());
    }
    else
    {
      exprt tmp_dest=sizeof_rec(type.subtype());

      if(tmp_dest.is_nil())
        return tmp_dest;

      mp_integer a, b;

      if(!to_integer(tmp_dest, a) &&
         !to_integer(size_expr, b))
      {
        dest=from_integer(a*b, size_type());
      }
      else
      {
        dest.id(ID_mult);
        dest.type()=size_type();
        dest.copy_to_operands(size_expr);
        dest.move_to_operands(tmp_dest);
        c_implicit_typecast(dest.op0(), dest.type(), ns);
        c_implicit_typecast(dest.op1(), dest.type(), ns);
      }
    }
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    dest=from_integer(0, size_type());
    
    mp_integer bit_field_width=0;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &sub_type=ns.follow(it->type());

      if(it->get_bool(ID_is_type))
      {
      }
      else if(sub_type.id()==ID_code)
      {
      }
      else if(it->get_is_bit_field())
      {
        // this needs to be a signedbv/unsignedbv/enum
        if(sub_type.id()!=ID_signedbv &&
           sub_type.id()!=ID_unsignedbv &&
           sub_type.id()!=ID_c_enum)
          return nil_exprt();
          
        // We just sum them up.
        // This assumes they are properly padded.
        bit_field_width+=sub_type.get_int(ID_width);
      }
      else
      {
        exprt tmp=sizeof_rec(sub_type);

        if(tmp.is_nil())
          return tmp;

        dest=plus_exprt(dest, tmp);
      }
    }
    
    if(bit_field_width!=0)
      dest=plus_exprt(dest, from_integer(bit_field_width/8, size_type()));
  }
  else if(type.id()==ID_union)
  {
    // the empty union will have size 0
    exprt max_size=from_integer(0, size_type());
    
    const union_typet::componentst &components=
      to_union_type(type).components();

    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_bool(ID_is_type) || it->type().id()==ID_code)
        continue;

      const typet &sub_type=it->type();

      {
        exprt tmp=sizeof_rec(sub_type);

        if(tmp.is_nil())
          return nil_exprt();
          
        if(max_size.is_nil())
          max_size=tmp;
        else
          max_size=if_exprt(
            binary_relation_exprt(max_size, ID_lt, tmp),
            tmp, max_size);

        simplify(max_size, ns);
      }
    }

    dest=max_size;
  }
  else if(type.id()==ID_symbol)
  {
    return sizeof_rec(ns.follow(type));
  }
  else if(type.id()==ID_empty)
  {
    // gcc says that sizeof(void)==1, ISO C doesn't
    dest=from_integer(1, size_type());
  }
  else if(type.id()==ID_vector)
  {
    // simply multiply
    const exprt &size_expr=
      to_vector_type(type).size();
      
    exprt tmp_dest=sizeof_rec(type.subtype());

    if(tmp_dest.is_nil())
      return tmp_dest;

    mp_integer a, b;

    if(!to_integer(tmp_dest, a) &&
       !to_integer(size_expr, b))
    {
      dest=from_integer(a*b, size_type());
    }
    else
    {
      dest.id(ID_mult);
      dest.type()=size_type();
      dest.copy_to_operands(size_expr);
      dest.move_to_operands(tmp_dest);
      c_implicit_typecast(dest.op0(), dest.type(), ns);
      c_implicit_typecast(dest.op1(), dest.type(), ns);
    }
  }
  else if(type.id()==ID_complex)
  {
    // this is a pair

    exprt tmp_dest=sizeof_rec(type.subtype());

    if(tmp_dest.is_nil())
      return tmp_dest;

    mp_integer a;

    if(!to_integer(tmp_dest, a))
      dest=from_integer(a*2, size_type());
    else
      return nil_exprt();
  }
  else
  {
    // We give up; this shouldn't really happen on 'proper' C types,
    // but we do have some artificial ones that simply have no
    // meaningful size.
    dest.make_nil();
  }
  
  return dest;
}

/*******************************************************************\

Function: c_sizeoft::c_offsetof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_sizeoft::c_offsetof(
  const struct_typet &type,
  const irep_idt &component_name)
{
  const struct_typet::componentst &components=
    type.components();

  exprt dest=from_integer(0, size_type());
  
  mp_integer bit_field_width=0;

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    if(it->get_name()==component_name)
    {
      // done
      if(bit_field_width!=0)
        dest=plus_exprt(dest, from_integer(bit_field_width/8, size_type()));
      return dest;
    }
  
    if(it->get_bool(ID_is_type))
      continue;
      
    const typet &sub_type=ns.follow(it->type());

    if(sub_type.id()==ID_code)
    {
    }
    else if(it->get_is_bit_field())
    {
      // this needs to be a signedbv/unsignedbv
      // or an enum
      if(sub_type.id()!=ID_signedbv &&
         sub_type.id()!=ID_unsignedbv &&
         sub_type.id()!=ID_c_enum)
        return nil_exprt();
        
      // We just sum them up.
      // This assumes they are properly padded.
      bit_field_width+=sub_type.get_int(ID_width);
    }
    else
    {
      exprt tmp=sizeof_rec(sub_type);

      if(tmp.is_nil())
        return tmp;

      exprt sum=plus_exprt(dest, tmp);
      dest=sum;
    }
  }

  return nil_exprt();
}

/*******************************************************************\

Function: c_sizeof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_sizeof(const typet &src, const namespacet &ns)
{
  c_sizeoft c_sizeof_inst(ns);
  exprt tmp=c_sizeof_inst(src);
  simplify(tmp, ns);
  return tmp;
}

/*******************************************************************\

Function: c_offsetof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_offsetof(
  const struct_typet &src,
  const irep_idt &component_name,
  const namespacet &ns)
{
  c_sizeoft c_sizeof_inst(ns);
  exprt tmp=c_sizeof_inst.c_offsetof(src, component_name);
  simplify(tmp, ns);
  return tmp;
}

