/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_STRING_CONSTANT_H
#define CPROVER_UTIL_STRING_CONSTANT_H

#include "std_expr.h"
#include "expr.h"

class string_constantt : public nullary_exprt
{
public:
  DEPRECATED("use string_constantt(value) instead")
  string_constantt();

  explicit string_constantt(const irep_idt &value);

  void set_value(const irep_idt &value);

  const irep_idt &get_value() const
  {
    return get(ID_value);
  }

  array_exprt to_array_expr() const;
  bool from_array_expr(const array_exprt &);
};

inline const string_constantt &to_string_constant(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_constant);
  return static_cast<const string_constantt &>(expr);
}

inline string_constantt &to_string_constant(exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_constant);
  return static_cast<string_constantt &>(expr);
}

#endif // CPROVER_ANSI_C_STRING_CONSTANT_H
