/*******************************************************************\

Module: C/C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <std_expr.h>
#include <arith_tools.h>

#include "string_constant.h"
#include "concatenate_strings.h"

/*******************************************************************\

Function: concatenate_array_strings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concatenate_array_strings(
  array_exprt &dest,
  const array_exprt &other)
{
  assert(dest.type().id()==ID_array);
  assert(other.type().id()==ID_array);
  assert(dest.type().subtype()==other.type().subtype());

  exprt::operandst &dest_op=dest.operands();
  const exprt::operandst &other_op=other.operands();

  // dest must be zero-terminated  
  assert(dest_op.size()!=0);
  
  dest_op.reserve(dest_op.size()+other_op.size()-1);
  
  dest_op.pop_back();
  
  for(exprt::operandst::const_iterator
      it=other_op.begin(); it!=other_op.end(); it++)
    dest_op.push_back(*it);
    
  // adjust size
  exprt &size=to_array_type(dest.type()).size();
  size=from_integer(dest_op.size(), size.type());
}

/*******************************************************************\

Function: concatenate_strings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concatenate_strings(exprt &dest, const exprt &other)
{
  // both are standard strings?
  
  if(dest.id()==ID_string_constant &&
     other.id()==ID_string_constant)
  {
    dest.set(ID_value,
      dest.get_string(ID_value)+other.get_string(ID_value));
  }
  else if(dest.id()==ID_array && other.id()==ID_array)
  {
    // both are wide
    concatenate_array_strings(
      to_array_expr(dest), to_array_expr(other));
  }
  else if(dest.id()==ID_array && other.id()==ID_string_constant)
  {
    // dest is wide, other isn't, we first need to convert
    array_exprt other_tmp=to_string_constant(other).to_array_expr();
    
    exprt::operandst &other_op=other_tmp.operands();
    
    for(exprt::operandst::iterator
        it=other_op.begin(); it!=other_op.end(); it++)
    {
      // need to convert
      mp_integer value;
      if(to_integer(*it, value))
        assert(false);
      *it=from_integer(value, dest.type().subtype());
    }
    
    other_tmp.type()=dest.type();
    
    concatenate_array_strings(
      to_array_expr(dest), other_tmp);
  }
  else if(dest.id()==ID_string_constant && other.id()==ID_array)
  {
    // other is wide, dest isn't, we first need to convert
    
    array_exprt dest_tmp=to_string_constant(dest).to_array_expr();
    
    exprt::operandst &dest_op=dest_tmp.operands();

    for(exprt::operandst::iterator
        it=dest_op.begin(); it!=dest_op.end(); it++)
    {
      // need to convert
      mp_integer value;
      if(to_integer(*it, value))
        assert(false);
      *it=from_integer(value, other.type().subtype());
    }

    dest_tmp.type()=other.type();
    
    concatenate_array_strings(
      dest_tmp, to_array_expr(other));
      
    dest=dest_tmp;
  }
  else
  {
    // shouldn't happen
    assert(false);
  }
}
