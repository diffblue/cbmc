/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// expr2cleanct

#ifndef CPROVER_ANSI_C_EXPR2CLEANC_H
#define CPROVER_ANSI_C_EXPR2CLEANC_H

#include "expr2c_class.h"

#include <string>

/// Produces C from expression and types.
/// It does not print padding components in structs
/// It does not print array sizes when printing array types
/// It does not print the body of the struct when printing the struct type
class expr2cleanct:public expr2ct
{
public:
  explicit expr2cleanct(const namespacet &ns)
  : expr2ct(ns)
  {}

  std::string convert_with_identifier(
    const typet &src, const std::string &identifier);

protected:
  std::string convert_struct(
    const exprt &src, unsigned &precedence) override;

  std::string convert_struct_type(
    const typet &src,
    const std::string &qualifer_str,
    const std::string &declarator_str) override;

  std::string convert_array_type(
    const typet &src,
    const qualifierst &qualifiers,
    const std::string &declarator_str) override;

  std::string convert_constant_bool(bool boolean_value) override;
};

#endif // CPROVER_ANSI_C_EXPR2CLEANC_H
