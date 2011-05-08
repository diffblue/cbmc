/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <std_expr.h>

#include "string_constant.h"
#include "c_types.h"

/*******************************************************************\

Function: string_constantt::set_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

string_constantt::string_constantt():
  exprt(ID_string_constant)
{
  set_value(irep_idt());
  type()=typet(ID_array);
  type().subtype()=char_type();
}

/*******************************************************************\

Function: string_constantt::set_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_constantt::set_value(const irep_idt &value)
{
  exprt size_expr=from_integer(value.size()+1, int_type());
  type().add(ID_size).swap(size_expr);
  set(ID_value, value);
}

/*******************************************************************\

Function: string_constantt:to_array_expr

  Inputs:

 Outputs:

 Purpose: convert string into array constant

\*******************************************************************/

array_exprt string_constantt::to_array_expr() const
{
  const std::string &str=get_string(ID_value);
  unsigned string_size=str.size()+1; // zero
  const typet &char_type=type().subtype();
  bool char_is_unsigned=char_type.id()==ID_unsignedbv;

  exprt size=from_integer(string_size, index_type());

  array_exprt dest;
  dest.type()=array_typet();
  dest.type().subtype()=char_type;
  dest.type().set(ID_size, size);

  dest.operands().resize(string_size);

  exprt::operandst::iterator it=dest.operands().begin();
  for(unsigned i=0; i<string_size; i++, it++)
  {
    int ch=i==string_size-1?0:str[i];

    if(char_is_unsigned)
      ch=(unsigned char)ch;

    exprt &op=*it;

    op=from_integer(ch, char_type);

    if(ch>=32 && ch<=126)
    {
      char ch_str[2];
      ch_str[0]=ch;
      ch_str[1]=0;

      op.set(ID_C_cformat, "'"+std::string(ch_str)+"'");
    }
  }
  
  return dest;
}

