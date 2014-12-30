/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/std_expr.h>

#include "string_constant.h"
#include "c_types.h"

/*******************************************************************\

Function: string_constantt::string_constantt

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

Function: string_constantt::string_constantt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

string_constantt::string_constantt(const irep_idt &_value):
  exprt(ID_string_constant)
{
  set_value(_value);
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
  exprt size_expr=from_integer(value.size()+1, index_type());
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
  unsigned string_size=str.size()+1; // we add the zero
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
    // Are we at the end? Do implicit zero.
    int ch=i==string_size-1?0:str[i];

    if(char_is_unsigned)
      ch=(unsigned char)ch;

    exprt &op=*it;

    op=from_integer(ch, char_type);

    if(ch>=32 && ch<=126)
    {
      std::string ch_str="'";
      if(ch=='\'' || ch=='\\') ch_str+='\\';
      ch_str+=(char)ch;
      ch_str+="'";

      op.set(ID_C_cformat, ch_str);
    }
  }
  
  return dest;
}

/*******************************************************************\

Function: string_constantt:from_array_expr

  Inputs:

 Outputs: true on error

 Purpose: convert array constant into string

\*******************************************************************/

bool string_constantt::from_array_expr(const array_exprt &src)
{
  id(ID_string_constant);
  type()=src.type();
  
  const typet &subtype=type().subtype();

  // check subtype
  if(subtype!=signed_char_type() &&
     subtype!=unsigned_char_type())
    return true;
  
  std::string value;
  
  forall_operands(it, src)
  {
    mp_integer int_value=0;
    if(to_integer(*it, int_value)) return true;
    long long_value=integer2long(int_value);
    value+=(char)long_value;
  }
  
  // Drop the implicit zero at the end.
  // Not clear what the semantics should be if it's not there.
  if(!value.empty() && value[value.size()-1]==0)
    value.resize(value.size()-1);
    
  set_value(value);
  
  return false;
}

