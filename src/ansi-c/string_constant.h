/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STRING_CONSTANT_H
#define CPROVER_STRING_CONSTANT_H

#include <std_expr.h>
#include <expr.h>

class string_constantt:public exprt
{
public:
  string_constantt();

  friend inline const string_constantt &to_string_constant(const exprt &expr)
  {
    assert(expr.id()==ID_string_constant);
    return static_cast<const string_constantt &>(expr);
  }

  friend inline string_constantt &to_string_constant(exprt &expr)
  {
    assert(expr.id()==ID_string_constant);
    return static_cast<string_constantt &>(expr);
  }
  
  void set_value(const irep_idt &value);

  inline const irep_idt &get_value() const
  {
    return get(ID_value);
  }
  
  array_exprt to_array_expr() const;
};

const string_constantt &to_string_constant(const exprt &expr);
string_constantt &to_string_constant(exprt &expr);

#endif
