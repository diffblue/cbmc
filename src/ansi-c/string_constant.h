/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_STRING_CONSTANT_H
#define CPROVER_ANSI_C_STRING_CONSTANT_H

#include <util/std_expr.h>
#include <util/expr.h>

class string_constantt:public exprt
{
public:
  string_constantt();
  explicit string_constantt(const irep_idt &value);

  void set_value(const irep_idt &value);

  inline const irep_idt &get_value() const
  {
    return get(ID_value);
  }

  array_exprt to_array_expr() const;
  bool from_array_expr(const array_exprt &);
};

inline const string_constantt &to_string_constant(const exprt &expr)
{
  assert(expr.id()==ID_string_constant);
  return static_cast<const string_constantt &>(expr);
}

inline string_constantt &to_string_constant(exprt &expr)
{
  assert(expr.id()==ID_string_constant);
  return static_cast<string_constantt &>(expr);
}

#endif // CPROVER_ANSI_C_STRING_CONSTANT_H
