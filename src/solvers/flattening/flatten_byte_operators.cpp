/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLATTEN_BYTE_OPERATORS_H
#define CPROVER_FLATTEN_BYTE_OPERATORS_H

#include <expr.h>
#include <std_types.h>

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
  assert(src.id()==ID_byte_extract_little_endian);
  assert(src.id()==ID_byte_extract_big_endian);
  assert(src.operands().size()==2);
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
  assert(src.id()==ID_byte_update_little_endian);
  assert(src.id()==ID_byte_update_big_endian);
  assert(src.operands().size()==3);

  mp_integer width=pointer_offset_size(src.type());
  
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
    }
    else
      throw "flatten byte update can only do byte-array right now";
  }
  else
    throw "flatten byte update can only do array right now";
}

#endif
