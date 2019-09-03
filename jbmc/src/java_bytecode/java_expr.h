/*******************************************************************\

Module: Java-specific exprt subclasses

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Java-specific exprt subclasses

#ifndef CPROVER_JAVA_BYTECODE_JAVA_EXPR_H
#define CPROVER_JAVA_BYTECODE_JAVA_EXPR_H

#include <util/std_expr.h>

class java_instanceof_exprt : public binary_predicate_exprt
{
public:
  java_instanceof_exprt(exprt lhs, const struct_tag_typet &target_type)
    : binary_predicate_exprt(
        std::move(lhs),
        ID_java_instanceof,
        type_exprt(target_type))
  {
  }

  const exprt &tested_expr() const
  {
    return op0();
  }
  exprt &tested_expr()
  {
    return op0();
  }

  const struct_tag_typet &target_type() const
  {
    return to_struct_tag_type(op1().type());
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_predicate_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_predicate_exprt::validate(expr, ns, vm);

    const auto &expr_binary = static_cast<const binary_predicate_exprt &>(expr);

    DATA_CHECK(
      vm,
      can_cast_expr<type_exprt>(expr_binary.rhs()),
      "java_instanceof_exprt rhs should be a type_exprt");
    DATA_CHECK(
      vm,
      can_cast_type<struct_tag_typet>(expr_binary.rhs().type()),
      "java_instanceof_exprt rhs should denote a struct_tag_typet");
  }
};

template <>
inline bool can_cast_expr<java_instanceof_exprt>(const exprt &base)
{
  return can_cast_expr<binary_exprt>(base) && base.id() == ID_java_instanceof;
}

inline void validate_expr(const java_instanceof_exprt &value)
{
  java_instanceof_exprt::check(value);
}

/// \brief Cast an exprt to a \ref java_instanceof_exprt
///
/// \a expr must be known to be \ref java_instanceof_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref java_instanceof_exprt
inline const java_instanceof_exprt &to_java_instanceof_expr(const exprt &expr)
{
  java_instanceof_exprt::check(expr);
  PRECONDITION(can_cast_expr<java_instanceof_exprt>(expr));
  return static_cast<const java_instanceof_exprt &>(expr);
}

/// \copydoc to_java_instanceof_expr(const exprt &)
inline java_instanceof_exprt &to_java_instanceof_expr(exprt &expr)
{
  java_instanceof_exprt::check(expr);
  PRECONDITION(can_cast_expr<java_instanceof_exprt>(expr));
  return static_cast<java_instanceof_exprt &>(expr);
}

#endif // CPROVER_JAVA_BYTECODE_JAVA_EXPR_H
