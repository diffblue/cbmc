/*******************************************************************\

Module: Data structures representing statements in a program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_STD_CODE_BASE_H
#define CPROVER_UTIL_STD_CODE_BASE_H

#include "expr_cast.h"
#include "invariant.h"
#include "std_types.h"
#include "validate.h"
#include "validate_code.h"

/// Data structure for representing an arbitrary statement in a program. Every
/// specific type of statement (e.g. block of statements, assignment,
/// if-then-else statement...) is represented by a subtype of `codet`.
/// `codet`s are represented to be subtypes of \ref exprt since statements can
/// occur in an expression context in C: for example, the assignment `x = y;`
/// is an expression with return value `y`. For other types of statements in an
/// expression context, see e.g.
/// https://gcc.gnu.org/onlinedocs/gcc/Statement-Exprs.html.
/// To distinguish a `codet` from other [exprts](\ref exprt), we set its
/// [id()](\ref irept::id) to `ID_code`. To distinguish different types of
/// `codet`, we use a named sub `ID_statement`.
class codet : public exprt
{
public:
  /// \param statement: Specifies the type of the `codet` to be constructed,
  ///   e.g. `ID_block` for a \ref code_blockt or `ID_assign` for a
  ///   \ref code_frontend_assignt.
  explicit codet(const irep_idt &statement) : exprt(ID_code, empty_typet())
  {
    set_statement(statement);
  }

  codet(const irep_idt &statement, source_locationt loc)
    : exprt(ID_code, empty_typet(), std::move(loc))
  {
    set_statement(statement);
  }

  /// \param statement: Specifies the type of the `codet` to be constructed,
  ///   e.g. `ID_block` for a \ref code_blockt or `ID_assign` for a
  ///   \ref code_frontend_assignt.
  /// \param _op: any operands to be added
  explicit codet(const irep_idt &statement, operandst _op) : codet(statement)
  {
    operands() = std::move(_op);
  }

  codet(const irep_idt &statement, operandst op, source_locationt loc)
    : codet(statement, std::move(loc))
  {
    operands() = std::move(op);
  }

  void set_statement(const irep_idt &statement)
  {
    set(ID_statement, statement);
  }

  const irep_idt &get_statement() const
  {
    return get(ID_statement);
  }

  codet &first_statement();
  const codet &first_statement() const;
  codet &last_statement();
  const codet &last_statement() const;

  /// Check that the code statement is well-formed (shallow checks only, i.e.,
  /// enclosed statements, subexpressions, etc. are not checked)
  ///
  /// Subclasses may override this function to provide specific well-formedness
  /// checks for the corresponding types.
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  static void check(const codet &, const validation_modet)
  {
  }

  /// Check that the code statement is well-formed, assuming that all its
  /// enclosed statements, subexpressions, etc. have all ready been checked for
  /// well-formedness.
  ///
  /// Subclasses may override this function to provide specific well-formedness
  /// checks for the corresponding types.
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  static void validate(
    const codet &code,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check_code(code, vm);
  }

  /// Check that the code statement is well-formed (full check, including checks
  /// of all subexpressions)
  ///
  /// Subclasses may override this function to provide specific well-formedness
  /// checks for the corresponding types.
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  static void validate_full(
    const codet &code,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check_code(code, vm);
  }

  using exprt::op0;
  using exprt::op1;
  using exprt::op2;
  using exprt::op3;
};

namespace detail // NOLINT
{
template <typename Tag>
inline bool can_cast_code_impl(const exprt &expr, const Tag &tag)
{
  if(const auto ptr = expr_try_dynamic_cast<codet>(expr))
  {
    return ptr->get_statement() == tag;
  }
  return false;
}

} // namespace detail

template <>
inline bool can_cast_expr<codet>(const exprt &base)
{
  return base.id() == ID_code;
}

// to_code has no validation other than checking the id(), so no validate_expr
// is provided for codet

inline const codet &to_code(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_code);
  return static_cast<const codet &>(expr);
}

inline codet &to_code(exprt &expr)
{
  PRECONDITION(expr.id() == ID_code);
  return static_cast<codet &>(expr);
}

#endif // CPROVER_UTIL_STD_CODE_BASE_H
