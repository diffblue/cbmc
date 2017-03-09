/*******************************************************************\

Module: Symbol utilities

Author: Nathan Phillips, nathan.phillips@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_SYMBOL_UTILS_H
#define CPROVER_UTIL_SYMBOL_UTILS_H

#include <functional>
#include "namespace.h"
#include "std_expr.h"

// second: true <=> not found

class symbol_utilst
{
private:
  bool does_symbol_match(
    const exprt &lvalue,
    std::function<bool(symbolt)> predicate) const;
  const namespacet &ns;

public:
  explicit symbol_utilst(const namespacet &_ns):
  ns(_ns)
  {}

  bool is_parameter(const exprt &lvalue) const;
  bool is_static(const exprt &lvalue) const;
  bool is_auxiliary_variable(const exprt &lvalue) const;
  bool is_return_value_auxiliary(const exprt &lvalue) const;
};

#endif
