/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "string_constant.h"

#include "arith_tools.h"
#include "c_types.h"
#include "std_expr.h"

string_constantt::string_constantt() : nullary_exprt(ID_string_constant)
{
  set_value(irep_idt());
}

string_constantt::string_constantt(const irep_idt &_value)
  : nullary_exprt(ID_string_constant)
{
  set_value(_value);
}

void string_constantt::set_value(const irep_idt &value)
{
  exprt size_expr=from_integer(value.size()+1, index_type());
  type()=array_typet(char_type(), size_expr);
  set(ID_value, value);
}

/// convert string into array constant
array_exprt string_constantt::to_array_expr() const
{
  const std::string &str=get_string(ID_value);
  std::size_t string_size=str.size()+1; // we add the zero
  const typet &char_type=type().subtype();
  bool char_is_unsigned=char_type.id()==ID_unsignedbv;

  exprt size=from_integer(string_size, index_type());

  array_exprt dest;
  dest.type()=array_typet(char_type, size);

  dest.operands().resize(string_size);

  exprt::operandst::iterator it=dest.operands().begin();
  for(std::size_t i=0; i<string_size; i++, it++)
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
      if(ch=='\'' || ch=='\\')
        ch_str+='\\';
      ch_str+=static_cast<char>(ch);
      ch_str+="'";
    }
  }

  return dest;
}

/// convert array constant into string
/// \return true on error
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
    if(to_integer(*it, int_value))
      return true;
    unsigned unsigned_value=integer2unsigned(int_value);
    value+=static_cast<char>(unsigned_value);
  }

  // Drop the implicit zero at the end.
  // Not clear what the semantics should be if it's not there.
  if(!value.empty() && value[value.size()-1]==0)
    value.resize(value.size()-1);

  set_value(value);

  return false;
}
