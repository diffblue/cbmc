/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "string_constant.h"

#include "arith_tools.h"
#include "c_types.h"
#include "expr_util.h"
#include "pointer_expr.h"
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

std::optional<mp_integer> string_literal_length(const exprt &expr)
{
  // Peel off the (implicit) typecasts inserted by array-to-pointer decay.
  const exprt &current = skip_typecast(expr);

  // We only fold the bare-literal shape `&literal[0]`.  Any pointer
  // arithmetic (a non-zero index/offset) or a choice between literals must
  // not fold to a constant: doing so would silently drop the offset or pick
  // an arbitrary operand.  Such arguments fall back to the runtime model.
  const auto address_of = expr_try_dynamic_cast<address_of_exprt>(current);
  if(address_of == nullptr)
    return {};

  const auto index = expr_try_dynamic_cast<index_exprt>(address_of->object());
  if(index == nullptr)
    return {};

  const auto string = expr_try_dynamic_cast<string_constantt>(index->array());
  if(string == nullptr)
    return {};

  const auto offset = numeric_cast<mp_integer>(index->index());
  if(offset != mp_integer{0})
    return {};

  // strlen counts the bytes up to (but not including) the first NUL, which
  // need not be the end of the stored literal (e.g. "a\0b" has length 1).
  const std::string value = id2string(string->value());
  const std::size_t nul = value.find('\0');
  return mp_integer{nul == std::string::npos ? value.size() : nul};
}
