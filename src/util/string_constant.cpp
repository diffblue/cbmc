/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "string_constant.h"

#include "arith_tools.h"
#include "c_types.h"
#include "std_expr.h"

string_constantt::string_constantt(const irep_idt &_value)
  : nullary_exprt(ID_string_constant, typet())
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
  const typet &char_type = to_array_type(type()).subtype();
  bool char_is_unsigned=char_type.id()==ID_unsignedbv;

  exprt size=from_integer(string_size, index_type());

  array_exprt dest({}, array_typet(char_type, size));

  dest.operands().resize(string_size);

  exprt::operandst::iterator it=dest.operands().begin();
  for(std::size_t i=0; i<string_size; i++, it++)
  {
    // Are we at the end? Do implicit zero.
    int ch=i==string_size-1?0:str[i];

    if(char_is_unsigned)
      ch = (unsigned char)ch;
    else
      ch = (signed char)ch;

    *it = from_integer(ch, char_type);
  }

  return dest;
}
