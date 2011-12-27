/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr.h>
#include <std_types.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <pointer_offset_size.h>

#include "flatten_byte_operators.h"

/*******************************************************************\

Function: flatten_byte_extract

  Inputs:

 Outputs:

 Purpose: rewrite byte extraction from an array to byte extraction 
          from a concatenation of array index expressions

\*******************************************************************/

exprt flatten_byte_extract(
  const exprt &src,
  const namespacet &ns)
{
  assert(src.id()==ID_byte_extract_little_endian ||
         src.id()==ID_byte_extract_big_endian);
  assert(src.operands().size()==2);

  bool little_endian;
  
  if(src.id()==ID_byte_extract_little_endian)
    little_endian=true;
  else if(src.id()==ID_byte_extract_big_endian)
    little_endian=false;
  else
    assert(false);
  
  if(src.id()==ID_byte_extract_big_endian) 
    throw "byte_extract flattening of big endian not done yet";

  unsigned width=
    integer2long(pointer_offset_size(ns, src.type()));
  
  const typet &t=src.op0().type();
  
  if(t.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(t);
    const typet &subtype=array_type.subtype();
    
    // byte-array?
    if((subtype.id()==ID_unsignedbv ||
        subtype.id()==ID_signedbv) &&
       subtype.get_int(ID_width)==8)
    {
      // get 'width'-many bytes, and concatenate
      exprt::operandst op;
      op.resize(width);
      
      for(unsigned i=0; i<width; i++)
      {
        // the most significant byte comes first in the concatenation!
        unsigned offset_i=
          little_endian?(width-i-1):i;
        
        plus_exprt offset(from_integer(offset_i, src.op1().type()), src.op1());
        index_exprt index_expr(subtype);
        index_expr.array()=src.op0();
        index_expr.index()=offset;
        op[i]=index_expr;
      }
      
      if(width==1)
        return op[0];
      else // width>=2
      {
        concatenation_exprt concatenation(src.type());
        concatenation.operands().swap(op);
        return concatenation;
      }
    }
    else // non-byte array
    {
      const exprt &root=src.op0();
      const exprt &offset=src.op1();
      const typet &array_type=ns.follow(root.type());
      const typet &offset_type=ns.follow(offset.type());
      const typet &element_type=ns.follow(array_type.subtype());
      mp_integer element_width=pointer_offset_size(ns, element_type);
      
      if(element_width==-1) // failed
        throw "failed to flatten non-byte array with unknown element width";

      mp_integer result_width=pointer_offset_size(ns, src.type());
      mp_integer num_elements=(element_width+result_width-2)/element_width+1;

      // compute new root and offset
      concatenation_exprt concat(
        unsignedbv_typet(integer2long(element_width*8*num_elements)));

      exprt first_index=
        (element_width==1)?offset 
        : div_exprt(offset, from_integer(element_width, offset_type)); // 8*offset/el_w

      for(mp_integer i=num_elements; i>0; --i)
      {
        plus_exprt index(first_index, from_integer(i-1, offset_type));
        concat.copy_to_operands(index_exprt(root, index));
      }

      // the new offset is width%offset
      exprt new_offset=
        (element_width==1)?from_integer(0, offset_type):
        mod_exprt(offset, from_integer(element_width, offset_type));

      // build new byte-extract expression
      exprt tmp(src.id(), src.type());
      tmp.copy_to_operands(concat, new_offset);

      return tmp;
    }
  }
  else // non-array
  {
    // We turn that into logical right shift and extractbits
    
    const exprt &offset=src.op1();
    const typet &offset_type=ns.follow(offset.type());

    mult_exprt times_eight(offset, from_integer(8, offset_type));
        
    lshr_exprt left_shift(src.op0(), times_eight);

    extractbits_exprt extractbits;
    
    extractbits.src()=left_shift;
    extractbits.type()=src.type();
    extractbits.upper()=from_integer(width*8-1, offset_type);
    extractbits.lower()=from_integer(0, offset_type);
      
    return extractbits;
  }
}

/*******************************************************************\

Function: flatten_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt flatten_byte_update(
  const exprt &src,
  const namespacet &ns)
{
  assert(src.id()==ID_byte_update_little_endian ||
         src.id()==ID_byte_update_big_endian);
  assert(src.operands().size()==3);

  unsigned width=
    integer2long(pointer_offset_size(ns, src.op2().type()));
  
  const typet &t=ns.follow(src.op0().type());
  
  if(t.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(t);
    const typet &subtype=array_type.subtype();
    
    // array of scalars?
    if(subtype.id()==ID_unsignedbv ||
       subtype.id()==ID_signedbv)
    {
      unsigned sub_width=subtype.get_int(ID_width);

      // byte array?
      if(sub_width==8)
      {
        // apply 'array-update-with' width times
        exprt result=src.op0();
        
        for(unsigned i=0; i<width; i++)
        {
          exprt i_expr=from_integer(i, ns.follow(src.op1().type()));

          exprt new_value;
          
          if(i==0 && width==1) // bytes?
          {
            new_value=src.op2();
            if(new_value.type()!=subtype)
              new_value.make_typecast(subtype);
          }
          else
          {
            exprt byte_extract_expr(
              src.id()==ID_byte_update_little_endian?ID_byte_extract_little_endian:
              src.id()==ID_byte_update_big_endian?ID_byte_extract_big_endian:
              throw "unexpected src.id()",
              subtype);
            
            byte_extract_expr.copy_to_operands(src.op2(), i_expr);
            new_value=flatten_byte_extract(byte_extract_expr, ns);
          }

          exprt where=plus_exprt(src.op1(), i_expr);
            
          with_exprt with_expr;
          with_expr.type()=src.type();
          with_expr.old()=result;
          with_expr.where()=where;
          with_expr.new_value()=new_value;
          
          result.swap(with_expr);
        }
        
        return result;
      }
      else
      {
        throw "flatten_byte_update can only do byte-array right now";
      }
    }
    else
    {
      throw "flatten_byte_update can only do arrays of scalars right now";
    }
  }
  else
    throw "flatten_byte_update can only do array right now";
}

/*******************************************************************\

Function: has_byte_operators

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_byte_operator(const exprt &src)
{
  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian ||
     src.id()==ID_byte_extract_little_endian ||
     src.id()==ID_byte_extract_big_endian)
    return true;
  
  forall_operands(it, src)
    if(has_byte_operator(*it)) return true;
  
  return false;
}

/*******************************************************************\

Function: flatten_byte_operators

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt flatten_byte_operators(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  
  // destroys any sharing, should use hash table
  Forall_operands(it, tmp)
  {
    exprt tmp=flatten_byte_operators(*it, ns);
    it->swap(tmp);
  }

  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian)
    return flatten_byte_update(tmp, ns);
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
    return flatten_byte_extract(tmp, ns);
  else
    return tmp;
}
