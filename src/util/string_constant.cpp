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
  // Peel off (implicit) typecasts, and the left operands of comma operators
  // as long as no side effects are lost.
  const auto skip = [](const exprt &e) -> const exprt &
  {
    const exprt *result = &skip_typecast(e);
    while(result->id() == ID_comma && result->operands().size() == 2 &&
          !has_subexpr(to_binary_expr(*result).op0(), ID_side_effect))
    {
      result = &skip_typecast(to_binary_expr(*result).op1());
    }
    return *result;
  };

  const exprt *current = &skip(expr);

  // `literal + offset` (or `offset + literal`) with a constant offset
  mp_integer offset = 0;
  if(current->id() == ID_plus && current->operands().size() == 2)
  {
    const exprt &op0 = to_plus_expr(*current).op0();
    const exprt &op1 = to_plus_expr(*current).op1();
    const bool pointer0 = op0.type().id() == ID_pointer;
    const auto summand = numeric_cast<mp_integer>(pointer0 ? op1 : op0);
    if(!summand.has_value())
      return {};
    offset = *summand;
    current = &skip(pointer0 ? op0 : op1);
  }

  // `&literal[index]` with a constant index, which is what array-to-pointer
  // decay produces.  A choice between literals or a non-constant offset must
  // not fold to a constant.
  const auto address_of = expr_try_dynamic_cast<address_of_exprt>(*current);
  if(address_of == nullptr)
    return {};

  const auto index = expr_try_dynamic_cast<index_exprt>(address_of->object());
  if(index == nullptr)
    return {};

  const auto string =
    expr_try_dynamic_cast<string_constantt>(skip(index->array()));
  if(string == nullptr)
    return {};

  const auto index_value = numeric_cast<mp_integer>(index->index());
  if(!index_value.has_value())
    return {};
  offset += *index_value;

  // the offset must be within the literal, including its terminating NUL
  const std::string value = id2string(string->value());
  if(offset < 0 || offset > mp_integer{value.size()})
    return {};

  // strlen counts the bytes up to (but not including) the first NUL, which
  // need not be the end of the stored literal (e.g. "a\0b" has length 1).
  const std::size_t start = numeric_cast_v<std::size_t>(offset);
  const std::size_t nul = value.find('\0', start);
  return mp_integer{(nul == std::string::npos ? value.size() : nul) - start};
}
