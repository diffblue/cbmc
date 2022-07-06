/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_STRING_CONSTANT_H
#define CPROVER_UTIL_STRING_CONSTANT_H

#include "std_expr.h"

class string_constantt : public nullary_exprt
{
public:
  explicit string_constantt(const irep_idt &value);

  void set_value(const irep_idt &value);

  const irep_idt &get_value() const
  {
    return get(ID_value);
  }

  array_exprt to_array_expr() const;
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

#endif // CPROVER_ANSI_C_STRING_CONSTANT_H
