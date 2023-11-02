/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "string_constant.h"

#include "arith_tools.h"
#include "c_types.h"
#include "std_expr.h"

static array_typet make_type(const irep_idt &value)
{
  exprt size_expr = from_integer(value.size() + 1, c_index_type());
  return array_typet(char_type(), size_expr);
}

string_constantt::string_constantt(const irep_idt &_value)
  : nullary_exprt(ID_string_constant, make_type(_value))
{
  value(_value);
}

void string_constantt::value(const irep_idt &_value)
{
  exprt::type() = make_type(_value);
  set(ID_value, _value);
}

const array_typet &string_constantt::type() const
{
  return to_array_type(exprt::type());
}

array_typet &string_constantt::type()
{
  return to_array_type(exprt::type());
}

/// convert string into array constant
array_exprt string_constantt::to_array_expr() const
{
  const std::string &str=get_string(ID_value);
  std::size_t string_size=str.size()+1; // we add the zero
  const typet &char_type = string_constantt::char_type();
  bool char_is_unsigned=char_type.id()==ID_unsignedbv;

  exprt size = from_integer(string_size, c_index_type());

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

  return std::move(dest).with_source_location(*this);
}
