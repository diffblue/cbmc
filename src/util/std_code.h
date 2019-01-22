/*******************************************************************\

Module: Data structures representing statements in a program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_STD_CODE_H
#define CPROVER_UTIL_STD_CODE_H

#include <list>

#include "base_type.h"
#include "expr.h"
#include "expr_cast.h"
#include "invariant.h"
#include "std_expr.h"
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
class codet:public exprt
{
public:
  DEPRECATED("use codet(statement) instead")
  codet():exprt(ID_code, typet(ID_code))
  {
  }

  /// \param statement: Specifies the type of the `codet` to be constructed,
  ///   e.g. `ID_block` for a \ref code_blockt or `ID_assign` for a
  ///   \ref code_assignt.
  explicit codet(const irep_idt &statement):
    exprt(ID_code, typet(ID_code))
  {
    set_statement(statement);
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
  class code_blockt &make_block();

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
};

namespace detail // NOLINT
{

template<typename Tag>
inline bool can_cast_code_impl(const exprt &expr, const Tag &tag)
{
  if(const auto ptr = expr_try_dynamic_cast<codet>(expr))
  {
    return ptr->get_statement() == tag;
  }
  return false;
}

} // namespace detail

template<> inline bool can_cast_expr<codet>(const exprt &base)
{
  return base.id()==ID_code;
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

/// A \ref codet representing sequential composition of program statements.
/// Each operand represents a statement in the block.
class code_blockt:public codet
{
public:
  code_blockt():codet(ID_block)
  {
  }

  typedef std::vector<codet> code_operandst;

  code_operandst &statements()
  {
    return (code_operandst &)get_sub();
  }

  const code_operandst &statements() const
  {
    return (const code_operandst &)get_sub();
  }

  static code_blockt from_list(const std::list<codet> &_list)
  {
    code_blockt result;
    auto &s=result.statements();
    s.reserve(_list.size());
    for(const auto &c : _list)
      s.push_back(c);
    return result;
  }

  explicit code_blockt(const std::vector<codet> &_statements):codet(ID_block)
  {
    operands()=(const std::vector<exprt> &)_statements;
  }

  explicit code_blockt(std::vector<codet> &&_statements):codet(ID_block)
  {
    operands()=std::move((std::vector<exprt> &&)_statements);
  }

  void add(const codet &code)
  {
    add_to_operands(code);
  }

  void add(codet &&code)
  {
    add_to_operands(std::move(code));
  }

  void add(codet code, const source_locationt &loc)
  {
    code.add_source_location() = loc;
    add(code);
  }

  void append(const code_blockt &extra_block);

  // This is the closing '}' or 'END' at the end of a block
  source_locationt end_location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_end_location));
  }

  codet &find_last_statement();
};

template<> inline bool can_cast_expr<code_blockt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_block);
}

// to_code_block has no validation other than checking the statement(), so no
// validate_expr is provided for code_blockt

inline const code_blockt &to_code_block(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_block);
  return static_cast<const code_blockt &>(code);
}

inline code_blockt &to_code_block(codet &code)
{
  PRECONDITION(code.get_statement() == ID_block);
  return static_cast<code_blockt &>(code);
}

/// A \ref codet representing a `skip` statement.
class code_skipt:public codet
{
public:
  code_skipt():codet(ID_skip)
  {
  }
};

template<> inline bool can_cast_expr<code_skipt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_skip);
}

// there is no to_code_skip, so no validate_expr is provided for code_skipt

/// A \ref codet representing an assignment in the program.
/// For example, if an expression `e1` is represented as an \ref exprt `expr1`
/// and an expression `e2` is represented as an \ref exprt `expr2`, the
/// assignment `e1 = e2;` can be represented as `code_assignt(expr1, expr2)`.
class code_assignt:public codet
{
public:
  code_assignt():codet(ID_assign)
  {
    operands().resize(2);
  }

  code_assignt(const exprt &lhs, const exprt &rhs):codet(ID_assign)
  {
    add_to_operands(lhs, rhs);
  }

  exprt &lhs()
  {
    return op0();
  }

  exprt &rhs()
  {
    return op1();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  const exprt &rhs() const
  {
    return op1();
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, code.operands().size() == 2, "assignment must have two operands");
  }

  static void validate(
    const codet &code,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(code, vm);

    DATA_CHECK(
      vm,
      base_type_eq(code.op0().type(), code.op1().type(), ns),
      "lhs and rhs of assignment must have same type");
  }

  static void validate_full(
    const codet &code,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    for(const exprt &op : code.operands())
    {
      validate_full_expr(op, ns, vm);
    }

    validate(code, ns, vm);
  }
};

template<> inline bool can_cast_expr<code_assignt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assign);
}

inline void validate_expr(const code_assignt & x)
{
  validate_operands(x, 2, "assignment must have two operands");
}

inline const code_assignt &to_code_assign(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assign);
  code_assignt::check(code);
  return static_cast<const code_assignt &>(code);
}

inline code_assignt &to_code_assign(codet &code)
{
  PRECONDITION(code.get_statement() == ID_assign);
  code_assignt::check(code);
  return static_cast<code_assignt &>(code);
}

/// A `codet` representing the declaration of a local variable.
/// For example, if a variable (symbol) `x` is represented as a
/// \ref symbol_exprt `sym`, then the declaration of this variable can be
/// represented as `code_declt(sym)`.
class code_declt:public codet
{
public:
  explicit code_declt(const symbol_exprt &symbol) : codet(ID_decl)
  {
    add_to_operands(symbol);
  }

  symbol_exprt &symbol()
  {
    return static_cast<symbol_exprt &>(op0());
  }

  const symbol_exprt &symbol() const
  {
    return static_cast<const symbol_exprt &>(op0());
  }

  const irep_idt &get_identifier() const
  {
    return symbol().get_identifier();
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, code.operands().size() == 1, "declaration must have one operand");
    DATA_CHECK(
      vm,
      code.op0().id() == ID_symbol,
      "declaring a non-symbol: " +
        id2string(to_symbol_expr(code.op0()).get_identifier()));
  }
};

template<> inline bool can_cast_expr<code_declt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_decl);
}

inline void validate_expr(const code_declt &x)
{
  validate_operands(x, 1, "decls must have one or more operands", true);
}

inline const code_declt &to_code_decl(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_decl);

  // will be size()==1 in the future
  DATA_INVARIANT(
    code.operands().size() >= 1, "decls must have one or more operands");
  DATA_INVARIANT(
    code.op0().id() == ID_symbol, "decls symbols must be a \"symbol\"");

  return static_cast<const code_declt &>(code);
}

inline code_declt &to_code_decl(codet &code)
{
  PRECONDITION(code.get_statement() == ID_decl);

  // will be size()==1 in the future
  DATA_INVARIANT(
    code.operands().size() >= 1, "decls must have one or more operands");
  return static_cast<code_declt &>(code);
}

/// A \ref codet representing the removal of a local variable going out of
/// scope.
class code_deadt:public codet
{
public:
  explicit code_deadt(const symbol_exprt &symbol) : codet(ID_dead)
  {
    add_to_operands(symbol);
  }

  symbol_exprt &symbol()
  {
    return static_cast<symbol_exprt &>(op0());
  }

  const symbol_exprt &symbol() const
  {
    return static_cast<const symbol_exprt &>(op0());
  }

  const irep_idt &get_identifier() const
  {
    return symbol().get_identifier();
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      code.operands().size() == 1,
      "removal (code_deadt) must have one operand");
    DATA_CHECK(
      vm,
      code.op0().id() == ID_symbol,
      "removing a non-symbol: " +
        id2string(to_symbol_expr(code.op0()).get_identifier()) + "from scope");
  }
};

template<> inline bool can_cast_expr<code_deadt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_dead);
}

inline void validate_expr(const code_deadt &x)
{
  validate_operands(x, 1, "dead statement must have one operand");
}

inline const code_deadt &to_code_dead(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_dead);
  DATA_INVARIANT(
    code.operands().size() == 1, "dead statement must have one operand");
  DATA_INVARIANT(
    to_unary_expr(code).op().id() == ID_symbol,
    "dead statement must take symbol operand");
  return static_cast<const code_deadt &>(code);
}

inline code_deadt &to_code_dead(codet &code)
{
  PRECONDITION(code.get_statement() == ID_dead);
  DATA_INVARIANT(
    code.operands().size() == 1, "dead statement must have one operand");
  DATA_INVARIANT(
    to_unary_expr(code).op().id() == ID_symbol,
    "dead statement must take symbol operand");
  return static_cast<code_deadt &>(code);
}

/// An assumption, which must hold in subsequent code.
class code_assumet:public codet
{
public:
  DEPRECATED("use code_assumet(expr) instead")
  code_assumet():codet(ID_assume)
  {
    operands().resize(1);
  }

  explicit code_assumet(const exprt &expr):codet(ID_assume)
  {
    add_to_operands(expr);
  }

  const exprt &assumption() const
  {
    return op0();
  }

  exprt &assumption()
  {
    return op0();
  }
};

template<> inline bool can_cast_expr<code_assumet>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assume);
}

// to_code_assume only checks the code statement, so no validate_expr is
// provided for code_assumet

inline const code_assumet &to_code_assume(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assume);
  return static_cast<const code_assumet &>(code);
}

inline code_assumet &to_code_assume(codet &code)
{
  PRECONDITION(code.get_statement() == ID_assume);
  return static_cast<code_assumet &>(code);
}

inline void validate_expr(const code_assumet &x)
{
  validate_operands(x, 1, "assume must have one operand");
}

/// A non-fatal assertion, which checks a condition then permits execution to
/// continue.
class code_assertt:public codet
{
public:
  DEPRECATED("use code_assertt(expr) instead")
  code_assertt():codet(ID_assert)
  {
    operands().resize(1);
  }

  explicit code_assertt(const exprt &expr):codet(ID_assert)
  {
    add_to_operands(expr);
  }

  const exprt &assertion() const
  {
    return op0();
  }

  exprt &assertion()
  {
    return op0();
  }
};

template<> inline bool can_cast_expr<code_assertt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assert);
}

// to_code_assert only checks the code statement, so no validate_expr is
// provided for code_assertt

inline const code_assertt &to_code_assert(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assert);
  return static_cast<const code_assertt &>(code);
}

inline code_assertt &to_code_assert(codet &code)
{
  PRECONDITION(code.get_statement() == ID_assert);
  return static_cast<code_assertt &>(code);
}

inline void validate_expr(const code_assertt &x)
{
  validate_operands(x, 1, "assert must have one operand");
}

/// Create a fatal assertion, which checks a condition and then halts if it does
/// not hold. Equivalent to `ASSERT(condition); ASSUME(condition)`.
///
/// Source level assertions should probably use this, whilst checks that are
/// normally non-fatal at runtime, such as integer overflows, should use
/// code_assertt by itself.
/// \param condition: condition to assert
/// \param source_location: source location to attach to the generated code;
///   conventionally this should have `comment` and `property_class` fields set
///   to indicate the nature of the assertion.
/// \return A code block that asserts a condition then aborts if it does not
///   hold.
code_blockt create_fatal_assertion(
  const exprt &condition, const source_locationt &source_location);

/// \ref codet representation of an if-then-else statement.
class code_ifthenelset:public codet
{
public:
  DEPRECATED("use code_ifthenelset(condition, then_code[, else_code]) instead")
  code_ifthenelset():codet(ID_ifthenelse)
  {
    operands().resize(3);
    op1().make_nil();
    op2().make_nil();
  }

  /// An if \p condition then \p then_code else \p else_code statement.
  code_ifthenelset(
    const exprt &condition,
    const codet &then_code,
    const codet &else_code)
    : codet(ID_ifthenelse)
  {
    add_to_operands(condition, then_code, else_code);
  }

  /// An if \p condition then \p then_code statement (no "else" case).
  code_ifthenelset(const exprt &condition, const codet &then_code)
    : codet(ID_ifthenelse)
  {
    add_to_operands(condition, then_code, nil_exprt());
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const codet &then_case() const
  {
    return static_cast<const codet &>(op1());
  }

  bool has_else_case() const
  {
    return op2().is_not_nil();
  }

  const codet &else_case() const
  {
    return static_cast<const codet &>(op2());
  }

  codet &then_case()
  {
    return static_cast<codet &>(op1());
  }

  codet &else_case()
  {
    return static_cast<codet &>(op2());
  }
};

template<> inline bool can_cast_expr<code_ifthenelset>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_ifthenelse);
}

inline void validate_expr(const code_ifthenelset &x)
{
  validate_operands(x, 3, "if-then-else must have three operands");
}

inline const code_ifthenelset &to_code_ifthenelse(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_ifthenelse);
  DATA_INVARIANT(
    code.operands().size() == 3, "if-then-else must have three operands");
  return static_cast<const code_ifthenelset &>(code);
}

inline code_ifthenelset &to_code_ifthenelse(codet &code)
{
  PRECONDITION(code.get_statement() == ID_ifthenelse);
  DATA_INVARIANT(
    code.operands().size() == 3, "if-then-else must have three operands");
  return static_cast<code_ifthenelset &>(code);
}

/// \ref codet representing a `switch` statement.
class code_switcht:public codet
{
public:
  DEPRECATED("use code_switcht(value, body) instead")
  code_switcht():codet(ID_switch)
  {
    operands().resize(2);
  }

  code_switcht(const exprt &_value, const codet &_body) : codet(ID_switch)
  {
    operands().resize(2);
    value() = _value;
    body() = _body;
  }

  const exprt &value() const
  {
    return op0();
  }

  exprt &value()
  {
    return op0();
  }

  const codet &body() const
  {
    return to_code(op1());
  }

  codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

template<> inline bool can_cast_expr<code_switcht>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_switch);
}

inline void validate_expr(const code_switcht &x)
{
  validate_operands(x, 2, "switch must have two operands");
}

inline const code_switcht &to_code_switch(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_switch);
  DATA_INVARIANT(code.operands().size() == 2, "switch must have two operands");
  return static_cast<const code_switcht &>(code);
}

inline code_switcht &to_code_switch(codet &code)
{
  PRECONDITION(code.get_statement() == ID_switch);
  DATA_INVARIANT(code.operands().size() == 2, "switch must have two operands");
  return static_cast<code_switcht &>(code);
}

/// \ref codet representing a `while` statement.
class code_whilet:public codet
{
public:
  DEPRECATED("use code_whilet(cond, body) instead")
  code_whilet():codet(ID_while)
  {
    operands().resize(2);
  }

  code_whilet(const exprt &_cond, const codet &_body) : codet(ID_while)
  {
    operands().resize(2);
    cond() = _cond;
    body() = _body;
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const codet &body() const
  {
    return to_code(op1());
  }

  codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

template<> inline bool can_cast_expr<code_whilet>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_while);
}

inline void validate_expr(const code_whilet &x)
{
  validate_operands(x, 2, "while must have two operands");
}

inline const code_whilet &to_code_while(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_while);
  DATA_INVARIANT(code.operands().size() == 2, "while must have two operands");
  return static_cast<const code_whilet &>(code);
}

inline code_whilet &to_code_while(codet &code)
{
  PRECONDITION(code.get_statement() == ID_while);
  DATA_INVARIANT(code.operands().size() == 2, "while must have two operands");
  return static_cast<code_whilet &>(code);
}

/// \ref codet representation of a `do while` statement.
class code_dowhilet:public codet
{
public:
  DEPRECATED("use code_dowhilet(cond, body) instead")
  code_dowhilet():codet(ID_dowhile)
  {
    operands().resize(2);
  }

  code_dowhilet(const exprt &_cond, const codet &_body) : codet(ID_dowhile)
  {
    operands().resize(2);
    cond() = _cond;
    body() = _body;
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const codet &body() const
  {
    return to_code(op1());
  }

  codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

template<> inline bool can_cast_expr<code_dowhilet>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_dowhile);
}

inline void validate_expr(const code_dowhilet &x)
{
  validate_operands(x, 2, "do-while must have two operands");
}

inline const code_dowhilet &to_code_dowhile(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_dowhile);
  DATA_INVARIANT(
    code.operands().size() == 2, "do-while must have two operands");
  return static_cast<const code_dowhilet &>(code);
}

inline code_dowhilet &to_code_dowhile(codet &code)
{
  PRECONDITION(code.get_statement() == ID_dowhile);
  DATA_INVARIANT(
    code.operands().size() == 2, "do-while must have two operands");
  return static_cast<code_dowhilet &>(code);
}

/// \ref codet representation of a `for` statement.
class code_fort:public codet
{
public:
  DEPRECATED("use code_fort(init, cond, iter, body) instead")
  code_fort():codet(ID_for)
  {
    operands().resize(4);
  }

  /// A statement describing a for loop with initializer \p _init, loop
  /// condition \p _cond, increment \p _iter, and body \p _body.
  code_fort(
    const exprt &_init,
    const exprt &_cond,
    const exprt &_iter,
    const codet &_body)
    : codet(ID_for)
  {
    reserve_operands(4);
    add_to_operands(_init, _cond, _iter);
    add_to_operands(_body);
  }

  // nil or a statement
  const exprt &init() const
  {
    return op0();
  }

  exprt &init()
  {
    return op0();
  }

  const exprt &cond() const
  {
    return op1();
  }

  exprt &cond()
  {
    return op1();
  }

  const exprt &iter() const
  {
    return op2();
  }

  exprt &iter()
  {
    return op2();
  }

  const codet &body() const
  {
    return to_code(op3());
  }

  codet &body()
  {
    return static_cast<codet &>(op3());
  }
};

template<> inline bool can_cast_expr<code_fort>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_for);
}

inline void validate_expr(const code_fort &x)
{
  validate_operands(x, 4, "for must have four operands");
}

inline const code_fort &to_code_for(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_for);
  DATA_INVARIANT(code.operands().size() == 4, "for must have four operands");
  return static_cast<const code_fort &>(code);
}

inline code_fort &to_code_for(codet &code)
{
  PRECONDITION(code.get_statement() == ID_for);
  DATA_INVARIANT(code.operands().size() == 4, "for must have four operands");
  return static_cast<code_fort &>(code);
}

/// \ref codet representation of a `goto` statement.
class code_gotot:public codet
{
public:
  DEPRECATED("use code_gotot(label) instead")
  code_gotot():codet(ID_goto)
  {
  }

  explicit code_gotot(const irep_idt &label):codet(ID_goto)
  {
    set_destination(label);
  }

  void set_destination(const irep_idt &label)
  {
    set(ID_destination, label);
  }

  const irep_idt &get_destination() const
  {
    return get(ID_destination);
  }
};

template<> inline bool can_cast_expr<code_gotot>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_goto);
}

inline void validate_expr(const code_gotot &x)
{
  validate_operands(x, 0, "goto must not have operands");
}

inline const code_gotot &to_code_goto(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_goto);
  DATA_INVARIANT(code.operands().empty(), "goto must not have operands");
  return static_cast<const code_gotot &>(code);
}

inline code_gotot &to_code_goto(codet &code)
{
  PRECONDITION(code.get_statement() == ID_goto);
  DATA_INVARIANT(code.operands().empty(), "goto must not have operands");
  return static_cast<code_gotot &>(code);
}

/// \ref codet representation of a function call statement.
/// The function call statement has three operands.
/// The first is the expression that is used to store the return value.
/// The second is the function called.
/// The third is a vector of argument values.
class code_function_callt:public codet
{
public:
  DEPRECATED("Use code_function_callt(...) instead")
  code_function_callt():codet(ID_function_call)
  {
    operands().resize(3);
    lhs().make_nil();
    op2().id(ID_arguments);
  }

  explicit code_function_callt(const exprt &_function) : codet(ID_function_call)
  {
    operands().resize(3);
    lhs().make_nil();
    op2().id(ID_arguments);
    function() = _function;
  }

  typedef exprt::operandst argumentst;

  code_function_callt(
    const exprt &_lhs,
    const exprt &_function,
    argumentst &&_arguments)
    : code_function_callt(_function)
  {
    lhs() = _lhs;
    arguments() = std::move(_arguments);
  }

  code_function_callt(
    const exprt &_lhs,
    const exprt &_function,
    const argumentst &_arguments)
    : code_function_callt(_function)
  {
    lhs() = _lhs;
    arguments() = _arguments;
  }

  code_function_callt(const exprt &_function, argumentst &&_arguments)
    : code_function_callt(_function)
  {
    arguments() = std::move(_arguments);
  }

  code_function_callt(const exprt &_function, const argumentst &_arguments)
    : code_function_callt(_function)
  {
    arguments() = _arguments;
  }

  exprt &lhs()
  {
    return op0();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  exprt &function()
  {
    return op1();
  }

  const exprt &function() const
  {
    return op1();
  }

  argumentst &arguments()
  {
    return op2().operands();
  }

  const argumentst &arguments() const
  {
    return op2().operands();
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      code.operands().size() == 3,
      "function calls must have three operands:\n1) expression to store the "
      "returned values\n2) the function being called\n3) the vector of "
      "arguments");
  }

  static void validate(
    const codet &code,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(code, vm);

    if(code.op0().id() == ID_nil)
      DATA_CHECK(
        vm,
        to_code_type(code.op1().type()).return_type().id() == ID_empty,
        "void function should not return value");
    else
      DATA_CHECK(
        vm,
        base_type_eq(
          code.op0().type(), to_code_type(code.op1().type()).return_type(), ns),
        "function returns expression of wrong type");
  }

  static void validate_full(
    const codet &code,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    for(const exprt &op : code.operands())
    {
      validate_full_expr(op, ns, vm);
    }

    validate(code, ns, vm);
  }
};

template<> inline bool can_cast_expr<code_function_callt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_function_call);
}

// to_code_function_call only checks the code statement, so no validate_expr is
// provided for code_function_callt

inline const code_function_callt &to_code_function_call(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_function_call);
  return static_cast<const code_function_callt &>(code);
}

inline code_function_callt &to_code_function_call(codet &code)
{
  PRECONDITION(code.get_statement() == ID_function_call);
  return static_cast<code_function_callt &>(code);
}

inline void validate_expr(const code_function_callt &x)
{
  validate_operands(x, 3, "function calls must have three operands");
}

/// \ref codet representation of a "return from a function" statement.
class code_returnt:public codet
{
public:
  code_returnt():codet(ID_return)
  {
    operands().resize(1);
    op0().make_nil();
  }

  explicit code_returnt(const exprt &_op):codet(ID_return)
  {
    add_to_operands(_op);
  }

  const exprt &return_value() const
  {
    return op0();
  }

  exprt &return_value()
  {
    return op0();
  }

  bool has_return_value() const
  {
    if(operands().empty())
      return false; // backwards compatibility
    return return_value().is_not_nil();
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(vm, code.operands().size() == 1, "return must have one operand");
  }
};

template<> inline bool can_cast_expr<code_returnt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_return);
}

// to_code_return only checks the code statement, so no validate_expr is
// provided for code_returnt

inline const code_returnt &to_code_return(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_return);
  return static_cast<const code_returnt &>(code);
}

inline code_returnt &to_code_return(codet &code)
{
  PRECONDITION(code.get_statement() == ID_return);
  return static_cast<code_returnt &>(code);
}

inline void validate_expr(const code_returnt &x)
{
  validate_operands(x, 1, "return must have one operand");
}

/// \ref codet representation of a label for branch targets.
class code_labelt:public codet
{
public:
  DEPRECATED("use code_labelt(label) instead")
  code_labelt():codet(ID_label)
  {
    operands().resize(1);
  }

  explicit code_labelt(const irep_idt &_label):codet(ID_label)
  {
    operands().resize(1);
    set_label(_label);
  }

  code_labelt(
    const irep_idt &_label, const codet &_code):codet(ID_label)
  {
    operands().resize(1);
    set_label(_label);
    code()=_code;
  }

  const irep_idt &get_label() const
  {
    return get(ID_label);
  }

  void set_label(const irep_idt &label)
  {
    set(ID_label, label);
  }

  codet &code()
  {
    return static_cast<codet &>(op0());
  }

  const codet &code() const
  {
    return static_cast<const codet &>(op0());
  }
};

template<> inline bool can_cast_expr<code_labelt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_label);
}

inline void validate_expr(const code_labelt &x)
{
  validate_operands(x, 1, "label must have one operand");
}

inline const code_labelt &to_code_label(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_label);
  DATA_INVARIANT(code.operands().size() == 1, "label must have one operand");
  return static_cast<const code_labelt &>(code);
}

inline code_labelt &to_code_label(codet &code)
{
  PRECONDITION(code.get_statement() == ID_label);
  DATA_INVARIANT(code.operands().size() == 1, "label must have one operand");
  return static_cast<code_labelt &>(code);
}

/// \ref codet representation of a switch-case, i.e.\ a `case` statement within
/// a `switch`.
class code_switch_caset:public codet
{
public:
  DEPRECATED("use code_switch_caset(case_op, code) instead")
  code_switch_caset():codet(ID_switch_case)
  {
    operands().resize(2);
  }

  code_switch_caset(
    const exprt &_case_op, const codet &_code):codet(ID_switch_case)
  {
    add_to_operands(_case_op, _code);
  }

  bool is_default() const
  {
    return get_bool(ID_default);
  }

  void set_default()
  {
    return set(ID_default, true);
  }

  const exprt &case_op() const
  {
    return op0();
  }

  exprt &case_op()
  {
    return op0();
  }

  codet &code()
  {
    return static_cast<codet &>(op1());
  }

  const codet &code() const
  {
    return static_cast<const codet &>(op1());
  }
};

template<> inline bool can_cast_expr<code_switch_caset>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_switch_case);
}

inline void validate_expr(const code_switch_caset &x)
{
  validate_operands(x, 2, "switch-case must have two operands");
}

inline const code_switch_caset &to_code_switch_case(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_switch_case);
  DATA_INVARIANT(
    code.operands().size() == 2, "switch-case must have two operands");
  return static_cast<const code_switch_caset &>(code);
}

inline code_switch_caset &to_code_switch_case(codet &code)
{
  PRECONDITION(code.get_statement() == ID_switch_case);
  DATA_INVARIANT(
    code.operands().size() == 2, "switch-case must have two operands");
  return static_cast<code_switch_caset &>(code);
}

/// \ref codet representation of a `break` statement (within a `for` or `while`
/// loop).
class code_breakt:public codet
{
public:
  code_breakt():codet(ID_break)
  {
  }
};

template<> inline bool can_cast_expr<code_breakt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_break);
}

// to_code_break only checks the code statement, so no validate_expr is
// provided for code_breakt

inline const code_breakt &to_code_break(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_break);
  return static_cast<const code_breakt &>(code);
}

inline code_breakt &to_code_break(codet &code)
{
  PRECONDITION(code.get_statement() == ID_break);
  return static_cast<code_breakt &>(code);
}

/// \ref codet representation of a `continue` statement (within a `for` or
/// `while` loop).
class code_continuet:public codet
{
public:
  code_continuet():codet(ID_continue)
  {
  }
};

template<> inline bool can_cast_expr<code_continuet>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_continue);
}

// to_code_continue only checks the code statement, so no validate_expr is
// provided for code_continuet

inline const code_continuet &to_code_continue(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_continue);
  return static_cast<const code_continuet &>(code);
}

inline code_continuet &to_code_continue(codet &code)
{
  PRECONDITION(code.get_statement() == ID_continue);
  return static_cast<code_continuet &>(code);
}

/// \ref codet representation of an inline assembler statement.
class code_asmt:public codet
{
public:
  code_asmt():codet(ID_asm)
  {
  }

  explicit code_asmt(const exprt &expr):codet(ID_asm)
  {
    add_to_operands(expr);
  }

  const irep_idt &get_flavor() const
  {
    return get(ID_flavor);
  }

  void set_flavor(const irep_idt &f)
  {
    set(ID_flavor, f);
  }
};

template<> inline bool can_cast_expr<code_asmt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_asm);
}

// to_code_asm only checks the code statement, so no validate_expr is
// provided for code_asmt

inline code_asmt &to_code_asm(codet &code)
{
  PRECONDITION(code.get_statement() == ID_asm);
  return static_cast<code_asmt &>(code);
}

inline const code_asmt &to_code_asm(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_asm);
  return static_cast<const code_asmt &>(code);
}

/// \ref codet representation of an expression statement.
/// It has one operand, which is the expression it stores.
class code_expressiont:public codet
{
public:
  DEPRECATED("use code_expressiont(expr) instead")
  code_expressiont():codet(ID_expression)
  {
    operands().resize(1);
  }

  explicit code_expressiont(const exprt &expr):codet(ID_expression)
  {
    add_to_operands(expr);
  }

  const exprt &expression() const
  {
    return op0();
  }

  exprt &expression()
  {
    return op0();
  }
};

template<> inline bool can_cast_expr<code_expressiont>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_expression);
}

inline void validate_expr(const code_expressiont &x)
{
  validate_operands(x, 1, "expression statement must have one operand");
}

inline code_expressiont &to_code_expression(codet &code)
{
  PRECONDITION(code.get_statement() == ID_expression);
  DATA_INVARIANT(
    code.operands().size() == 1, "expression statement must have one operand");
  return static_cast<code_expressiont &>(code);
}

inline const code_expressiont &to_code_expression(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_expression);
  DATA_INVARIANT(
    code.operands().size() == 1, "expression statement must have one operand");
  return static_cast<const code_expressiont &>(code);
}

/// An expression containing a side effect.
/// Note that unlike most classes in this file, `side_effect_exprt` and its
/// subtypes are not subtypes of \ref codet, but they inherit directly from
/// \ref exprt. They do have a `statement` like [codets](\ref codet), but their
/// [id()](\ref irept::id) is `ID_side_effect`, not `ID_code`.
class side_effect_exprt : public exprt
{
public:
  DEPRECATED("use side_effect_exprt(statement, type, loc) instead")
  explicit side_effect_exprt(const irep_idt &statement) : exprt(ID_side_effect)
  {
    set_statement(statement);
  }

  DEPRECATED("use side_effect_exprt(statement, type, loc) instead")
  side_effect_exprt(const irep_idt &statement, const typet &_type)
    : exprt(ID_side_effect, _type)
  {
    set_statement(statement);
  }

  side_effect_exprt(
    const irep_idt &statement,
    const typet &_type,
    const source_locationt &loc)
    : exprt(ID_side_effect, _type)
  {
    set_statement(statement);
    add_source_location() = loc;
  }

  /// constructor with operands
  side_effect_exprt(
    const irep_idt &statement,
    operandst &&_operands,
    const typet &_type,
    const source_locationt &loc)
    : exprt(ID_side_effect, _type)
  {
    set_statement(statement);
    operands() = std::move(_operands);
    add_source_location() = loc;
  }

  const irep_idt &get_statement() const
  {
    return get(ID_statement);
  }

  void set_statement(const irep_idt &statement)
  {
    return set(ID_statement, statement);
  }
};

namespace detail // NOLINT
{

template<typename Tag>
inline bool can_cast_side_effect_expr_impl(const exprt &expr, const Tag &tag)
{
  if(const auto ptr = expr_try_dynamic_cast<side_effect_exprt>(expr))
  {
    return ptr->get_statement() == tag;
  }
  return false;
}

} // namespace detail

template<> inline bool can_cast_expr<side_effect_exprt>(const exprt &base)
{
  return base.id()==ID_side_effect;
}

// to_side_effect_expr only checks the id, so no validate_expr is provided for
// side_effect_exprt

inline side_effect_exprt &to_side_effect_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_side_effect);
  return static_cast<side_effect_exprt &>(expr);
}

inline const side_effect_exprt &to_side_effect_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_side_effect);
  return static_cast<const side_effect_exprt &>(expr);
}

/// A \ref side_effect_exprt that returns a non-deterministically chosen value.
class side_effect_expr_nondett:public side_effect_exprt
{
public:
  DEPRECATED("use side_effect_expr_nondett(statement, type, loc) instead")
  side_effect_expr_nondett():side_effect_exprt(ID_nondet)
  {
    set_nullable(true);
  }

  DEPRECATED("use side_effect_expr_nondett(statement, type, loc) instead")
  explicit side_effect_expr_nondett(const typet &_type):
    side_effect_exprt(ID_nondet, _type)
  {
    set_nullable(true);
  }

  side_effect_expr_nondett(const typet &_type, const source_locationt &loc)
    : side_effect_exprt(ID_nondet, _type, loc)
  {
    set_nullable(true);
  }

  void set_nullable(bool nullable)
  {
    set(ID_is_nondet_nullable, nullable);
  }

  bool get_nullable() const
  {
    return get_bool(ID_is_nondet_nullable);
  }
};

template<>
inline bool can_cast_expr<side_effect_expr_nondett>(const exprt &base)
{
  return detail::can_cast_side_effect_expr_impl(base, ID_nondet);
}

// to_side_effect_expr_nondet only checks the id, so no validate_expr is
// provided for side_effect_expr_nondett

inline side_effect_expr_nondett &to_side_effect_expr_nondet(exprt &expr)
{
  auto &side_effect_expr_nondet=to_side_effect_expr(expr);
  PRECONDITION(side_effect_expr_nondet.get_statement() == ID_nondet);
  return static_cast<side_effect_expr_nondett &>(side_effect_expr_nondet);
}

inline const side_effect_expr_nondett &to_side_effect_expr_nondet(
  const exprt &expr)
{
  const auto &side_effect_expr_nondet=to_side_effect_expr(expr);
  PRECONDITION(side_effect_expr_nondet.get_statement() == ID_nondet);
  return static_cast<const side_effect_expr_nondett &>(side_effect_expr_nondet);
}

/// A \ref side_effect_exprt that performs an assignment
class side_effect_expr_assignt : public side_effect_exprt
{
public:
  /// construct an assignment side-effect, given lhs and rhs
  /// The type is copied from lhs
  side_effect_expr_assignt(
    const exprt &_lhs,
    const exprt &_rhs,
    const source_locationt &loc)
    : side_effect_exprt(ID_assign, {_lhs, _rhs}, _lhs.type(), loc)
  {
  }

  /// construct an assignment side-effect, given lhs, rhs and the type
  side_effect_expr_assignt(
    const exprt &_lhs,
    const exprt &_rhs,
    const typet &_type,
    const source_locationt &loc)
    : side_effect_exprt(ID_assign, {_lhs, _rhs}, _type, loc)
  {
  }

  /// construct an assignment side-effect, given lhs, rhs and the type
  side_effect_expr_assignt(
    exprt &&_lhs,
    exprt &&_rhs,
    typet &&_type,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_assign,
        {std::move(_lhs), std::move(_rhs)},
        std::move(_type),
        loc)
  {
  }

  exprt &lhs()
  {
    return op0();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  exprt &rhs()
  {
    return op1();
  }

  const exprt &rhs() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<side_effect_expr_assignt>(const exprt &base)
{
  return detail::can_cast_side_effect_expr_impl(base, ID_assign);
}

inline side_effect_expr_assignt &to_side_effect_expr_assign(exprt &expr)
{
  auto &side_effect_expr_assign = to_side_effect_expr(expr);
  PRECONDITION(side_effect_expr_assign.get_statement() == ID_assign);
  return static_cast<side_effect_expr_assignt &>(side_effect_expr_assign);
}

inline const side_effect_expr_assignt &
to_side_effect_expr_assign(const exprt &expr)
{
  const auto &side_effect_expr_assign = to_side_effect_expr(expr);
  PRECONDITION(side_effect_expr_assign.get_statement() == ID_assign);
  return static_cast<const side_effect_expr_assignt &>(side_effect_expr_assign);
}

/// A \ref side_effect_exprt representation of a function call side effect.
class side_effect_expr_function_callt:public side_effect_exprt
{
public:
  DEPRECATED(
    "use side_effect_expr_function_callt("
    "function, arguments, type, loc) instead")
  side_effect_expr_function_callt()
    : side_effect_exprt(ID_function_call, typet(), source_locationt())
  {
    operands().resize(2);
    op1().id(ID_arguments);
  }

  DEPRECATED(
    "use side_effect_expr_function_callt("
    "function, arguments, type, loc) instead")
  side_effect_expr_function_callt(
    const exprt &_function,
    const exprt::operandst &_arguments)
    : side_effect_exprt(ID_function_call)
  {
    operands().resize(2);
    op1().id(ID_arguments);
    function() = _function;
    arguments() = _arguments;
  }

  DEPRECATED(
    "use side_effect_expr_function_callt("
    "function, arguments, type, loc) instead")
  side_effect_expr_function_callt(
    const exprt &_function,
    const exprt::operandst &_arguments,
    const typet &_type)
    : side_effect_exprt(ID_function_call, _type)
  {
    operands().resize(2);
    op1().id(ID_arguments);
    function() = _function;
    arguments() = _arguments;
  }

  side_effect_expr_function_callt(
    const exprt &_function,
    const exprt::operandst &_arguments,
    const typet &_type,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_function_call,
        {_function, exprt(ID_arguments)},
        _type,
        loc)
  {
    arguments() = _arguments;
  }

  exprt &function()
  {
    return op0();
  }

  const exprt &function() const
  {
    return op0();
  }

  exprt::operandst &arguments()
  {
    return op1().operands();
  }

  const exprt::operandst &arguments() const
  {
    return op1().operands();
  }
};

template<>
inline bool can_cast_expr<side_effect_expr_function_callt>(const exprt &base)
{
  return detail::can_cast_side_effect_expr_impl(base, ID_function_call);
}

// to_side_effect_expr_function_call only checks the id, so no validate_expr is
// provided for side_effect_expr_function_callt

inline side_effect_expr_function_callt
  &to_side_effect_expr_function_call(exprt &expr)
{
  PRECONDITION(expr.id() == ID_side_effect);
  PRECONDITION(expr.get(ID_statement) == ID_function_call);
  return static_cast<side_effect_expr_function_callt &>(expr);
}

inline const side_effect_expr_function_callt
  &to_side_effect_expr_function_call(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_side_effect);
  PRECONDITION(expr.get(ID_statement) == ID_function_call);
  return static_cast<const side_effect_expr_function_callt &>(expr);
}

/// A \ref side_effect_exprt representation of a side effect that throws an
/// exception.
class side_effect_expr_throwt:public side_effect_exprt
{
public:
  DEPRECATED("use side_effect_expr_throwt(exception_list) instead")
  side_effect_expr_throwt():side_effect_exprt(ID_throw)
  {
  }

  side_effect_expr_throwt(
    const irept &exception_list,
    const typet &type,
    const source_locationt &loc)
    : side_effect_exprt(ID_throw, type, loc)
  {
    set(ID_exception_list, exception_list);
  }
};

template<>
inline bool can_cast_expr<side_effect_expr_throwt>(const exprt &base)
{
  return detail::can_cast_side_effect_expr_impl(base, ID_throw);
}

// to_side_effect_expr_throw only checks the id, so no validate_expr is
// provided for side_effect_expr_throwt

inline side_effect_expr_throwt &to_side_effect_expr_throw(exprt &expr)
{
  PRECONDITION(expr.id() == ID_side_effect);
  PRECONDITION(expr.get(ID_statement) == ID_throw);
  return static_cast<side_effect_expr_throwt &>(expr);
}

inline const side_effect_expr_throwt &to_side_effect_expr_throw(
  const exprt &expr)
{
  PRECONDITION(expr.id() == ID_side_effect);
  PRECONDITION(expr.get(ID_statement) == ID_throw);
  return static_cast<const side_effect_expr_throwt &>(expr);
}

/// Pushes an exception handler, of the form:
/// exception_tag1 -> label1
/// exception_tag2 -> label2
/// ...
/// When used in a GOTO program statement, the corresponding
/// opcode must be CATCH, and the statement's `targets` must
/// be in one-to-one correspondence with the exception tags.
/// The labels may be unspecified for the case where
/// there is no corresponding source-language label, in which
/// case the GOTO statement targets must be set at the same
/// time.
class code_push_catcht:public codet
{
public:
  code_push_catcht():codet(ID_push_catch)
  {
    set(ID_exception_list, irept(ID_exception_list));
  }

  class exception_list_entryt:public irept
  {
  public:
    exception_list_entryt()
    {
    }

    explicit exception_list_entryt(const irep_idt &tag)
    {
      set(ID_tag, tag);
    }

    exception_list_entryt(const irep_idt &tag, const irep_idt &label)
    {
      set(ID_tag, tag);
      set(ID_label, label);
    }

    void set_tag(const irep_idt &tag)
    {
      set(ID_tag, tag);
    }

    const irep_idt &get_tag() const {
      return get(ID_tag);
    }

    void set_label(const irep_idt &label)
    {
      set(ID_label, label);
    }

    const irep_idt &get_label() const {
      return get(ID_label);
    }
  };

  typedef std::vector<exception_list_entryt> exception_listt;

  code_push_catcht(
    const irep_idt &tag,
    const irep_idt &label):
    codet(ID_push_catch)
  {
    set(ID_exception_list, irept(ID_exception_list));
    exception_list().push_back(exception_list_entryt(tag, label));
  }

  exception_listt &exception_list() {
    return (exception_listt &)find(ID_exception_list).get_sub();
  }

  const exception_listt &exception_list() const {
    return (const exception_listt &)find(ID_exception_list).get_sub();
  }
};

template<> inline bool can_cast_expr<code_push_catcht>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_push_catch);
}

// to_code_push_catch only checks the code statement, so no validate_expr is
// provided for code_push_catcht

static inline code_push_catcht &to_code_push_catch(codet &code)
{
  PRECONDITION(code.get_statement() == ID_push_catch);
  return static_cast<code_push_catcht &>(code);
}

static inline const code_push_catcht &to_code_push_catch(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_push_catch);
  return static_cast<const code_push_catcht &>(code);
}

/// Pops an exception handler from the stack of active handlers
/// (i.e. whichever handler was most recently pushed by a
/// `code_push_catcht`).
class code_pop_catcht:public codet
{
public:
  code_pop_catcht():codet(ID_pop_catch)
  {
  }
};

template<> inline bool can_cast_expr<code_pop_catcht>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_pop_catch);
}

// to_code_pop_catch only checks the code statement, so no validate_expr is
// provided for code_pop_catcht

static inline code_pop_catcht &to_code_pop_catch(codet &code)
{
  PRECONDITION(code.get_statement() == ID_pop_catch);
  return static_cast<code_pop_catcht &>(code);
}

static inline const code_pop_catcht &to_code_pop_catch(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_pop_catch);
  return static_cast<const code_pop_catcht &>(code);
}

/// A statement that catches an exception, assigning the exception
/// in flight to an expression (e.g. Java catch(Exception e) might be expressed
/// landingpadt(symbol_expr("e", ...)))
class code_landingpadt:public codet
{
 public:
  code_landingpadt():codet(ID_exception_landingpad)
  {
    operands().resize(1);
  }
  explicit code_landingpadt(const exprt &catch_expr):
  codet(ID_exception_landingpad)
  {
    add_to_operands(catch_expr);
  }
  const exprt &catch_expr() const
  {
    return op0();
  }
  exprt &catch_expr()
  {
    return op0();
  }
};

template<> inline bool can_cast_expr<code_landingpadt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_exception_landingpad);
}

// to_code_landingpad only checks the code statement, so no validate_expr is
// provided for code_landingpadt

static inline code_landingpadt &to_code_landingpad(codet &code)
{
  PRECONDITION(code.get_statement() == ID_exception_landingpad);
  return static_cast<code_landingpadt &>(code);
}

static inline const code_landingpadt &to_code_landingpad(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_exception_landingpad);
  return static_cast<const code_landingpadt &>(code);
}

/// \ref codet representation of a try/catch block.
class code_try_catcht:public codet
{
public:
  DEPRECATED("use code_try_catcht(try_code) instead")
  code_try_catcht():codet(ID_try_catch)
  {
    operands().resize(1);
  }

  /// A statement representing try \p _try_code catch ...
  explicit code_try_catcht(const codet &_try_code) : codet(ID_try_catch)
  {
    add_to_operands(_try_code);
  }

  codet &try_code()
  {
    return static_cast<codet &>(op0());
  }

  const codet &try_code() const
  {
    return static_cast<const codet &>(op0());
  }

  code_declt &get_catch_decl(unsigned i)
  {
    PRECONDITION((2 * i + 2) < operands().size());
    return to_code_decl(to_code(operands()[2*i+1]));
  }

  const code_declt &get_catch_decl(unsigned i) const
  {
    PRECONDITION((2 * i + 2) < operands().size());
    return to_code_decl(to_code(operands()[2*i+1]));
  }

  codet &get_catch_code(unsigned i)
  {
    PRECONDITION((2 * i + 2) < operands().size());
    return to_code(operands()[2*i+2]);
  }

  const codet &get_catch_code(unsigned i) const
  {
    PRECONDITION((2 * i + 2) < operands().size());
    return to_code(operands()[2*i+2]);
  }

  void add_catch(const code_declt &to_catch, const codet &code_catch)
  {
    add_to_operands(to_catch, code_catch);
  }
};

template<> inline bool can_cast_expr<code_try_catcht>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_try_catch);
}

inline void validate_expr(const code_try_catcht &x)
{
  validate_operands(x, 3, "try-catch must have three or more operands", true);
}

inline const code_try_catcht &to_code_try_catch(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_try_catch);
  DATA_INVARIANT(
    code.operands().size() >= 3, "try-catch must have three or more operands");
  return static_cast<const code_try_catcht &>(code);
}

inline code_try_catcht &to_code_try_catch(codet &code)
{
  PRECONDITION(code.get_statement() == ID_try_catch);
  DATA_INVARIANT(
    code.operands().size() >= 3, "try-catch must have three or more operands");
  return static_cast<code_try_catcht &>(code);
}

#endif // CPROVER_UTIL_STD_CODE_H
