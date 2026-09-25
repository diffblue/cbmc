/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_STRING_CONSTANT_H
#define CPROVER_UTIL_STRING_CONSTANT_H

#include "mp_arith.h"
#include "std_expr.h"

#include <optional>

class string_constantt : public nullary_exprt
{
public:
  explicit string_constantt(const irep_idt &);

  void value(const irep_idt &);

  const irep_idt &value() const
  {
    return get(ID_value);
  }

  array_exprt to_array_expr() const;

  const typet &char_type() const
  {
    return type().element_type();
  }

  const array_typet &type() const;
  array_typet &type();
};

template <>
inline bool can_cast_expr<string_constantt>(const exprt &base)
{
  return base.id() == ID_string_constant;
}

inline void validate_expr(const string_constantt &expr)
{
  validate_operands(expr, 0, "String constants must not have operands");
}

inline const string_constantt &to_string_constant(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_constant);
  return static_cast<const string_constantt &>(expr);
}

inline const string_constantt &to_string_constant(const typet &type)
{
  return to_string_constant((const exprt &)type);
}

inline string_constantt &to_string_constant(exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_constant);
  return static_cast<string_constantt &>(expr);
}

inline string_constantt &to_string_constant(typet &type)
{
  return to_string_constant((exprt &)type);
}

/// If \p expr is the offset-zero decay of a string literal -- that is, an
/// optional sequence of typecasts wrapping `address_of(index(string_constant,
/// 0))` -- return the length of that literal as `strlen` would compute it: the
/// number of bytes up to, but not including, the first NUL.  Returns an empty
/// optional for anything else (a non-zero offset such as `"abc" + 1`, a
/// conditional between literals, or a non-literal argument), so that callers
/// can fall back to a runtime model rather than fold to a wrong constant.
std::optional<mp_integer> string_literal_length(const exprt &expr);

#endif // CPROVER_ANSI_C_STRING_CONSTANT_H
