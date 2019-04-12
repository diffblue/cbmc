/*******************************************************************\

Module: Java Bytecode

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Representation of a constant Java string

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERAL_EXPR_H
#define CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERAL_EXPR_H

#include <util/expr.h>

class java_string_literal_exprt : public exprt
{
public:
  explicit java_string_literal_exprt(const irep_idt &literal)
    : exprt(ID_java_string_literal)
  {
    set(ID_value, literal);
  }

  irep_idt value() const
  {
    return get(ID_value);
  }
};

template <>
inline bool can_cast_expr<java_string_literal_exprt>(const exprt &base)
{
  return base.id() == ID_java_string_literal;
}

#endif // CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERAL_EXPR_H
