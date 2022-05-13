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
class codet : public irept
{
public:
  using operandst = irept::subt;

  /// \param statement: Specifies the type of the `codet` to be constructed,
  ///   e.g. `ID_block` for a \ref code_blockt or `ID_assign` for a
  ///   \ref code_frontend_assignt.
  explicit codet(const irep_idt &statement) : irept(ID_code)
  {
    set_statement(statement);
  }

  codet(const irep_idt &statement, source_locationt loc) : irept(ID_code)
  {
    set_statement(statement);
    add_source_location() = std::move(loc);
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

  operandst &operands()
  {
    return (operandst &)get_sub();
  }

  const operandst &operands() const
  {
    return (const operandst &)get_sub();
  }

  const source_locationt &find_source_location() const;

  const source_locationt &source_location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }

  source_locationt &add_source_location()
  {
    return static_cast<source_locationt &>(add(ID_C_source_location));
  }

  exprt &op0()
  {
    return static_cast<exprt &>(operands().front());
  }

  exprt &op1()
  {
    return static_cast<exprt &>(operands()[1]);
  }

  exprt &op2()
  {
    return static_cast<exprt &>(operands()[2]);
  }

  exprt &op3()
  {
    return static_cast<exprt &>(operands()[3]);
  }

  const exprt &op0() const
  {
    return static_cast<const exprt &>(operands().front());
  }

  const exprt &op1() const
  {
    return static_cast<const exprt &>(operands()[1]);
  }

  const exprt &op2() const
  {
    return static_cast<const exprt &>(operands()[2]);
  }

  const exprt &op3() const
  {
    return static_cast<const exprt &>(operands()[3]);
  }

protected:
  codet &code_op0()
  {
    return static_cast<codet &>(operands().front());
  }

  codet &code_op1()
  {
    return static_cast<codet &>(operands()[1]);
  }

  codet &code_op2()
  {
    return static_cast<codet &>(operands()[2]);
  }

  codet &code_op3()
  {
    return static_cast<codet &>(operands()[3]);
  }

  const codet &code_op0() const
  {
    return static_cast<const codet &>(operands().front());
  }

  const codet &code_op1() const
  {
    return static_cast<const codet &>(operands()[1]);
  }

  const codet &code_op2() const
  {
    return static_cast<const codet &>(operands()[2]);
  }

  const codet &code_op3() const
  {
    return static_cast<const codet &>(operands()[3]);
  }

public:
  bool has_operands() const
  {
    return !operands().empty();
  }

  void add_to_operands(const codet &code)
  {
    operands().push_back(code);
  }

  void add_to_operands(const codet &code0, const codet &code1)
  {
    operands().push_back(code0);
    operands().push_back(code1);
  }

  void add_to_operands(const exprt &expr)
  {
    operands().push_back(expr);
  }

  const exprt &as_expr() const
  {
    return static_cast<const exprt &>(static_cast<const irept &>(*this));
  }
};

namespace detail // NOLINT
{
template <typename Tag>
inline bool can_cast_code_impl(const irept &irep, const Tag &tag)
{
  if(irep.id() == ID_code)
  {
    return static_cast<const codet &>(irep).get_statement() == tag;
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

inline const codet &to_code(const irept &src)
{
  PRECONDITION(src.id() == ID_code);
  return static_cast<const codet &>(src);
}

inline codet &to_code(irept &src)
{
  PRECONDITION(src.id() == ID_code);
  return static_cast<codet &>(src);
}

#endif // CPROVER_UTIL_STD_CODE_BASE_H
