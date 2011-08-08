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

 Purpose:

\*******************************************************************/

exprt flatten_byte_extract(
  const exprt &src,
  const namespacet &ns)
{
  assert(src.id()==ID_byte_extract_little_endian ||
         src.id()==ID_byte_extract_big_endian);
  assert(src.operands().size()==2);

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
      // get 'width'-bytes, and concatenate
      exprt::operandst op;
      op.resize(width);
      
      for(unsigned i=0; i<width; i++)
      {
        index_exprt index_expr(subtype);
        index_expr.array()=src.op0();
        index_expr.index()=from_integer(i, integer_typet());
        op[i]=index_expr;
      }
      
      if(width==1)
        return op[0];
      else
      {
        concatenation_exprt concatenation(src.type());
        concatenation.operands().swap(op);
        return concatenation;
      }
    }
    else
      throw "flatten_byte_extract can only do byte-array right now";
  }
  else
  {
    // we turn that into extractbits
    extract_bits_exprt extract_bits;
    
    
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
      // apply 'with' width times
      exprt result=src;
      
      for(unsigned i=0; i<width; i++)
      {
        exprt byte_extract_expr(
          src.id()==ID_byte_update_little_endian?ID_byte_extract_little_endian:
          src.id()==ID_byte_update_big_endian?ID_byte_extract_big_endian:
          throw "unexpected src.id()",
          subtype);
          
        exprt i_expr=from_integer(i, ns.follow(src.op1().type()));
          
        byte_extract_expr.copy_to_operands(src.op1(), i_expr);
          
        with_exprt with_expr;
        with_expr.type()=src.type();
        with_expr.old()=result;
        with_expr.where()=plus_exprt(src.op1(), i_expr);
        with_expr.new_value()=flatten_byte_extract(byte_extract_expr, ns);
      }
      
      return result;
    }
    else
      throw "flatten_byte_update can only do byte-array right now";
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
    flatten_byte_operators(*it, ns);

  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian)
    return flatten_byte_update(src, ns);
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
    return flatten_byte_extract(src, ns);
    
  return src;
}
