/*******************************************************************\

Module: Data structures representing statements in a program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_STD_CODE_H
#define CPROVER_UTIL_STD_CODE_H

#include <list>

#include "std_code_base.h"
#include "std_expr.h"

/// A \ref codet representing an assignment in the program.
/// For example, if an expression `e1` is represented as an \ref exprt `expr1`
/// and an expression `e2` is represented as an \ref exprt `expr2`, the
/// (nonstandard) assignment statement `e1 = e2;` can be represented
/// as `code_frontend_assignt(expr1, expr2)`.
class code_frontend_assignt : public codet
{
public:
  code_frontend_assignt() : codet(ID_assign)
  {
    operands().resize(2);
  }

  code_frontend_assignt(exprt lhs, exprt rhs)
    : codet(ID_assign, {std::move(lhs), std::move(rhs)})
  {
  }

  code_frontend_assignt(exprt lhs, exprt rhs, source_locationt loc)
    : codet(ID_assign, {std::move(lhs), std::move(rhs)}, std::move(loc))
  {
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
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(code, vm);

    DATA_CHECK(
      vm,
      code.op0().type() == code.op1().type(),
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

template <>
inline bool can_cast_expr<code_frontend_assignt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assign);
}

inline void validate_expr(const code_frontend_assignt &x)
{
  code_frontend_assignt::check(x);
}

inline const code_frontend_assignt &to_code_frontend_assign(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assign);
  code_frontend_assignt::check(code);
  return static_cast<const code_frontend_assignt &>(code);
}

inline code_frontend_assignt &to_code_frontend_assign(codet &code)
{
  PRECONDITION(code.get_statement() == ID_assign);
  code_frontend_assignt::check(code);
  return static_cast<code_frontend_assignt &>(code);
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

  explicit code_blockt(const std::vector<codet> &_statements)
    : codet(ID_block, (const std::vector<exprt> &)_statements)
  {
  }

  explicit code_blockt(std::vector<codet> &&_statements)
    : codet(ID_block, std::move((std::vector<exprt> &&) _statements))
  {
  }

  void add(const codet &code)
  {
    add_to_operands(code);
  }

  void add(codet &&code)
  {
    add_to_operands(std::move(code));
  }

  void add(codet code, source_locationt loc)
  {
    code.add_source_location().swap(loc);
    add(std::move(code));
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

/// An assumption, which must hold in subsequent code.
class code_assumet : public codet
{
public:
  explicit code_assumet(exprt expr) : codet(ID_assume, {std::move(expr)})
  {
  }

  const exprt &assumption() const
  {
    return op0();
  }

  exprt &assumption()
  {
    return op0();
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

template <>
inline bool can_cast_expr<code_assumet>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assume);
}

inline void validate_expr(const code_assumet &x)
{
  validate_operands(x, 1, "assume must have one operand");
}

inline const code_assumet &to_code_assume(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assume);
  const code_assumet &ret = static_cast<const code_assumet &>(code);
  validate_expr(ret);
  return ret;
}

inline code_assumet &to_code_assume(codet &code)
{
  PRECONDITION(code.get_statement() == ID_assume);
  code_assumet &ret = static_cast<code_assumet &>(code);
  validate_expr(ret);
  return ret;
}

/// A non-fatal assertion, which checks a condition then permits execution to
/// continue.
class code_assertt : public codet
{
public:
  explicit code_assertt(exprt expr) : codet(ID_assert, {std::move(expr)})
  {
  }

  const exprt &assertion() const
  {
    return op0();
  }

  exprt &assertion()
  {
    return op0();
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

template <>
inline bool can_cast_expr<code_assertt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assert);
}

inline void validate_expr(const code_assertt &x)
{
  validate_operands(x, 1, "assert must have one operand");
}

inline const code_assertt &to_code_assert(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assert);
  const code_assertt &ret = static_cast<const code_assertt &>(code);
  validate_expr(ret);
  return ret;
}

inline code_assertt &to_code_assert(codet &code)
{
  PRECONDITION(code.get_statement() == ID_assert);
  code_assertt &ret = static_cast<code_assertt &>(code);
  validate_expr(ret);
  return ret;
}

/// A \ref codet representing a `skip` statement.
class code_skipt:public codet
{
public:
  code_skipt():codet(ID_skip)
  {
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

template<> inline bool can_cast_expr<code_skipt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_skip);
}

// there is no to_code_skip, so no validate_expr is provided for code_skipt

/// A `codet` representing the declaration of a local variable.
/// For example, if a variable (symbol) `x` is represented as a
/// \ref symbol_exprt `sym`, then the declaration of this variable can be
/// represented as `code_frontend_declt(sym)`.
class code_frontend_declt : public codet
{
public:
  explicit code_frontend_declt(symbol_exprt symbol)
    : codet(ID_decl, {std::move(symbol)})
  {
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

  /// Returns the initial value to which the declared variable is initialized,
  /// or empty in the case where no initialisation is included.
  /// \note: Initial values may be present in the front end but they must be
  ///   separated into a separate assignment when used in a `goto_instructiont`.
  optionalt<exprt> initial_value() const
  {
    if(operands().size() < 2)
      return {};
    return {op1()};
  }

  /// Sets the value to which this declaration initializes the declared
  /// variable. Empty optional maybe passed to remove existing initialisation.
  /// \note: Initial values may be present in the front end but they must be
  ///   separated into a separate assignment when used in a `goto_instructiont`.
  void set_initial_value(optionalt<exprt> initial_value)
  {
    if(!initial_value)
    {
      operands().resize(1);
    }
    else if(operands().size() < 2)
    {
      PRECONDITION(operands().size() == 1);
      add_to_operands(std::move(*initial_value));
    }
    else
    {
      op1() = std::move(*initial_value);
    }
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    // will be size()==1 in the future
    DATA_CHECK(
      vm,
      code.operands().size() >= 1,
      "declaration must have one or more operands");
    DATA_CHECK(
      vm,
      code.op0().id() == ID_symbol,
      "declaring a non-symbol: " +
        id2string(to_symbol_expr(code.op0()).get_identifier()));
  }
};

template <>
inline bool can_cast_expr<code_frontend_declt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_decl);
}

inline void validate_expr(const code_frontend_declt &x)
{
  code_frontend_declt::check(x);
}

inline const code_frontend_declt &to_code_frontend_decl(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_decl);
  code_frontend_declt::check(code);
  return static_cast<const code_frontend_declt &>(code);
}

inline code_frontend_declt &to_code_frontend_decl(codet &code)
{
  PRECONDITION(code.get_statement() == ID_decl);
  code_frontend_declt::check(code);
  return static_cast<code_frontend_declt &>(code);
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
  /// An if \p condition then \p then_code else \p else_code statement.
  code_ifthenelset(exprt condition, codet then_code, codet else_code)
    : codet(
        ID_ifthenelse,
        {std::move(condition), std::move(then_code), std::move(else_code)})
  {
  }

  /// An if \p condition then \p then_code statement (no "else" case).
  code_ifthenelset(exprt condition, codet then_code)
    : codet(
        ID_ifthenelse,
        {std::move(condition), std::move(then_code), nil_exprt()})
  {
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_ifthenelset &ret = static_cast<const code_ifthenelset &>(code);
  validate_expr(ret);
  return ret;
}

inline code_ifthenelset &to_code_ifthenelse(codet &code)
{
  PRECONDITION(code.get_statement() == ID_ifthenelse);
  code_ifthenelset &ret = static_cast<code_ifthenelset &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representing a `switch` statement.
class code_switcht:public codet
{
public:
  code_switcht(exprt _value, codet _body)
    : codet(ID_switch, {std::move(_value), std::move(_body)})
  {
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_switcht &ret = static_cast<const code_switcht &>(code);
  validate_expr(ret);
  return ret;
}

inline code_switcht &to_code_switch(codet &code)
{
  PRECONDITION(code.get_statement() == ID_switch);
  code_switcht &ret = static_cast<code_switcht &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representing a `while` statement.
class code_whilet:public codet
{
public:
  code_whilet(exprt _cond, codet _body)
    : codet(ID_while, {std::move(_cond), std::move(_body)})
  {
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_whilet &ret = static_cast<const code_whilet &>(code);
  validate_expr(ret);
  return ret;
}

inline code_whilet &to_code_while(codet &code)
{
  PRECONDITION(code.get_statement() == ID_while);
  code_whilet &ret = static_cast<code_whilet &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a `do while` statement.
class code_dowhilet:public codet
{
public:
  code_dowhilet(exprt _cond, codet _body)
    : codet(ID_dowhile, {std::move(_cond), std::move(_body)})
  {
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_dowhilet &ret = static_cast<const code_dowhilet &>(code);
  validate_expr(ret);
  return ret;
}

inline code_dowhilet &to_code_dowhile(codet &code)
{
  PRECONDITION(code.get_statement() == ID_dowhile);
  code_dowhilet &ret = static_cast<code_dowhilet &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a `for` statement.
class code_fort:public codet
{
public:
  /// A statement describing a for loop with initializer \p _init, loop
  /// condition \p _cond, increment \p _iter, and body \p _body.
  code_fort(exprt _init, exprt _cond, exprt _iter, codet _body)
    : codet(
        ID_for,
        {std::move(_init),
         std::move(_cond),
         std::move(_iter),
         std::move(_body)})
  {
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

  /// Produce a code_fort representing:
  /// ```
  /// for(loop_index = start_index; loop_index < end_index; ++loop_index)
  ///    body
  /// ```
  /// \param start_index: The expression to start the counter at
  /// \param end_index: The exclusive limit of the loop
  /// \param loop_index: The pre-declared symbol to use as the counter
  /// \param body: The code that should be put in the body of the loop
  /// \param location: The source location using for the increment instruction
  static code_fort from_index_bounds(
    exprt start_index,
    exprt end_index,
    symbol_exprt loop_index,
    codet body,
    source_locationt location);

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_fort &ret = static_cast<const code_fort &>(code);
  validate_expr(ret);
  return ret;
}

inline code_fort &to_code_for(codet &code)
{
  PRECONDITION(code.get_statement() == ID_for);
  code_fort &ret = static_cast<code_fort &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a `goto` statement.
class code_gotot:public codet
{
public:
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_gotot &ret = static_cast<const code_gotot &>(code);
  validate_expr(ret);
  return ret;
}

inline code_gotot &to_code_goto(codet &code)
{
  PRECONDITION(code.get_statement() == ID_goto);
  code_gotot &ret = static_cast<code_gotot &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a "return from a function" statement.
class code_frontend_returnt : public codet
{
public:
  code_frontend_returnt() : codet(ID_return, {nil_exprt()})
  {
  }

  explicit code_frontend_returnt(exprt _op) : codet(ID_return, {std::move(_op)})
  {
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
    return return_value().is_not_nil();
  }

  static void check(
    const codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(vm, code.operands().size() == 1, "return must have one operand");
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

template <>
inline bool can_cast_expr<code_frontend_returnt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_return);
}

inline void validate_expr(const code_frontend_returnt &x)
{
  code_frontend_returnt::check(x);
}

inline const code_frontend_returnt &to_code_frontend_return(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_return);
  code_frontend_returnt::check(code);
  return static_cast<const code_frontend_returnt &>(code);
}

inline code_frontend_returnt &to_code_frontend_return(codet &code)
{
  PRECONDITION(code.get_statement() == ID_return);
  code_frontend_returnt::check(code);
  return static_cast<code_frontend_returnt &>(code);
}

/// \ref codet representation of a label for branch targets.
class code_labelt:public codet
{
public:
  code_labelt(const irep_idt &_label, codet _code)
    : codet(ID_label, {std::move(_code)})
  {
    set_label(_label);
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_labelt &ret = static_cast<const code_labelt &>(code);
  validate_expr(ret);
  return ret;
}

inline code_labelt &to_code_label(codet &code)
{
  PRECONDITION(code.get_statement() == ID_label);
  code_labelt &ret = static_cast<code_labelt &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a switch-case, i.e.\ a `case` statement within
/// a `switch`.
class code_switch_caset:public codet
{
public:
  code_switch_caset(exprt _case_op, codet _code)
    : codet(ID_switch_case, {std::move(_case_op), std::move(_code)})
  {
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_switch_caset &ret = static_cast<const code_switch_caset &>(code);
  validate_expr(ret);
  return ret;
}

inline code_switch_caset &to_code_switch_case(codet &code)
{
  PRECONDITION(code.get_statement() == ID_switch_case);
  code_switch_caset &ret = static_cast<code_switch_caset &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a switch-case, i.e.\ a `case` statement
/// within a `switch`. This is the variant that takes a range,
/// which is a gcc extension.
class code_gcc_switch_case_ranget : public codet
{
public:
  code_gcc_switch_case_ranget(exprt _lower, exprt _upper, codet _code)
    : codet(
        ID_gcc_switch_case_range,
        {std::move(_lower), std::move(_upper), std::move(_code)})
  {
  }

  /// lower bound of range
  const exprt &lower() const
  {
    return op0();
  }

  /// lower bound of range
  exprt &lower()
  {
    return op0();
  }

  /// upper bound of range
  const exprt &upper() const
  {
    return op1();
  }

  /// upper bound of range
  exprt &upper()
  {
    return op1();
  }

  /// the statement to be executed when the case applies
  codet &code()
  {
    return static_cast<codet &>(op2());
  }

  /// the statement to be executed when the case applies
  const codet &code() const
  {
    return static_cast<const codet &>(op2());
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

template <>
inline bool can_cast_expr<code_gcc_switch_case_ranget>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_gcc_switch_case_range);
}

inline void validate_expr(const code_gcc_switch_case_ranget &x)
{
  validate_operands(x, 3, "gcc-switch-case-range must have three operands");
}

inline const code_gcc_switch_case_ranget &
to_code_gcc_switch_case_range(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_gcc_switch_case_range);
  const code_gcc_switch_case_ranget &ret =
    static_cast<const code_gcc_switch_case_ranget &>(code);
  validate_expr(ret);
  return ret;
}

inline code_gcc_switch_case_ranget &to_code_gcc_switch_case_range(codet &code)
{
  PRECONDITION(code.get_statement() == ID_gcc_switch_case_range);
  code_gcc_switch_case_ranget &ret =
    static_cast<code_gcc_switch_case_ranget &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of a `break` statement (within a `for` or `while`
/// loop).
class code_breakt:public codet
{
public:
  code_breakt():codet(ID_break)
  {
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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

  explicit code_asmt(exprt expr) : codet(ID_asm, {std::move(expr)})
  {
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

/// \ref codet representation of an inline assembler statement,
/// for the gcc flavor.
class code_asm_gcct : public code_asmt
{
public:
  code_asm_gcct()
  {
    set_flavor(ID_gcc);
    operands().resize(5);
  }

  exprt &asm_text()
  {
    return op0();
  }

  const exprt &asm_text() const
  {
    return op0();
  }

  exprt &outputs()
  {
    return op1();
  }

  const exprt &outputs() const
  {
    return op1();
  }

  exprt &inputs()
  {
    return op2();
  }

  const exprt &inputs() const
  {
    return op2();
  }

  exprt &clobbers()
  {
    return op3();
  }

  const exprt &clobbers() const
  {
    return op3();
  }

  exprt &labels()
  {
    return operands()[4];
  }

  const exprt &labels() const
  {
    return operands()[4];
  }

protected:
  using code_asmt::op0;
  using code_asmt::op1;
  using code_asmt::op2;
  using code_asmt::op3;
};

template <>
inline bool can_cast_expr<code_asm_gcct>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_asm);
}

inline void validate_expr(const code_asm_gcct &x)
{
  validate_operands(x, 5, "code_asm_gcc must have five operands");
}

inline code_asm_gcct &to_code_asm_gcc(codet &code)
{
  PRECONDITION(code.get_statement() == ID_asm);
  PRECONDITION(to_code_asm(code).get_flavor() == ID_gcc);
  code_asm_gcct &ret = static_cast<code_asm_gcct &>(code);
  validate_expr(ret);
  return ret;
}

inline const code_asm_gcct &to_code_asm_gcc(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_asm);
  PRECONDITION(to_code_asm(code).get_flavor() == ID_gcc);
  const code_asm_gcct &ret = static_cast<const code_asm_gcct &>(code);
  validate_expr(ret);
  return ret;
}

/// \ref codet representation of an expression statement.
/// It has one operand, which is the expression it stores.
class code_expressiont:public codet
{
public:
  explicit code_expressiont(exprt expr)
    : codet(ID_expression, {std::move(expr)})
  {
  }

  const exprt &expression() const
  {
    return op0();
  }

  exprt &expression()
  {
    return op0();
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  code_expressiont &ret = static_cast<code_expressiont &>(code);
  validate_expr(ret);
  return ret;
}

inline const code_expressiont &to_code_expression(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_expression);
  const code_expressiont &ret = static_cast<const code_expressiont &>(code);
  validate_expr(ret);
  return ret;
}

/// An expression containing a side effect.
/// Note that unlike most classes in this file, `side_effect_exprt` and its
/// subtypes are not subtypes of \ref codet, but they inherit directly from
/// \ref exprt. They do have a `statement` like [codets](\ref codet), but their
/// [id()](\ref irept::id) is `ID_side_effect`, not `ID_code`.
class side_effect_exprt : public exprt
{
public:
  side_effect_exprt(
    const irep_idt &statement,
    operandst _operands,
    typet _type,
    source_locationt loc)
    : exprt(ID_side_effect, std::move(_type), std::move(loc))
  {
    set_statement(statement);
    operands() = std::move(_operands);
  }

  side_effect_exprt(
    const irep_idt &statement,
    typet _type,
    source_locationt loc)
    : exprt(ID_side_effect, std::move(_type), std::move(loc))
  {
    set_statement(statement);
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
  side_effect_expr_nondett(typet _type, source_locationt loc)
    : side_effect_exprt(ID_nondet, std::move(_type), std::move(loc))
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
    exprt _lhs,
    exprt _rhs,
    typet _type,
    source_locationt loc)
    : side_effect_exprt(
        ID_assign,
        {std::move(_lhs), std::move(_rhs)},
        std::move(_type),
        std::move(loc))
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

/// A \ref side_effect_exprt that contains a statement
class side_effect_expr_statement_expressiont : public side_effect_exprt
{
public:
  /// construct an assignment side-effect, given lhs, rhs and the type
  side_effect_expr_statement_expressiont(
    codet _code,
    typet _type,
    source_locationt loc)
    : side_effect_exprt(
        ID_statement_expression,
        {std::move(_code)},
        std::move(_type),
        std::move(loc))
  {
  }

  codet &statement()
  {
    return to_code(op0());
  }

  const codet &statement() const
  {
    return to_code(op0());
  }
};

template <>
inline bool
can_cast_expr<side_effect_expr_statement_expressiont>(const exprt &base)
{
  return detail::can_cast_side_effect_expr_impl(base, ID_statement_expression);
}

inline side_effect_expr_statement_expressiont &
to_side_effect_expr_statement_expression(exprt &expr)
{
  auto &side_effect_expr_statement_expression = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr_statement_expression.get_statement() ==
    ID_statement_expression);
  return static_cast<side_effect_expr_statement_expressiont &>(
    side_effect_expr_statement_expression);
}

inline const side_effect_expr_statement_expressiont &
to_side_effect_expr_statement_expression(const exprt &expr)
{
  const auto &side_effect_expr_statement_expression = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr_statement_expression.get_statement() ==
    ID_statement_expression);
  return static_cast<const side_effect_expr_statement_expressiont &>(
    side_effect_expr_statement_expression);
}

/// A \ref side_effect_exprt representation of a function call side effect.
class side_effect_expr_function_callt:public side_effect_exprt
{
public:
  side_effect_expr_function_callt(
    exprt _function,
    exprt::operandst _arguments,
    typet _type,
    source_locationt loc)
    : side_effect_exprt(
        ID_function_call,
        {std::move(_function),
         multi_ary_exprt{ID_arguments, std::move(_arguments), typet{}}},
        std::move(_type),
        std::move(loc))
  {
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
  side_effect_expr_throwt(
    irept exception_list,
    typet type,
    source_locationt loc)
    : side_effect_exprt(ID_throw, std::move(type), std::move(loc))
  {
    set(ID_exception_list, std::move(exception_list));
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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

  explicit code_landingpadt(exprt catch_expr)
    : codet(ID_exception_landingpad, {std::move(catch_expr)})
  {
  }

  const exprt &catch_expr() const
  {
    return op0();
  }
  exprt &catch_expr()
  {
    return op0();
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  /// A statement representing try \p _try_code catch ...
  explicit code_try_catcht(codet _try_code)
    : codet(ID_try_catch, {std::move(_try_code)})
  {
  }

  codet &try_code()
  {
    return static_cast<codet &>(op0());
  }

  const codet &try_code() const
  {
    return static_cast<const codet &>(op0());
  }

  code_frontend_declt &get_catch_decl(unsigned i)
  {
    PRECONDITION((2 * i + 2) < operands().size());
    return to_code_frontend_decl(to_code(operands()[2 * i + 1]));
  }

  const code_frontend_declt &get_catch_decl(unsigned i) const
  {
    PRECONDITION((2 * i + 2) < operands().size());
    return to_code_frontend_decl(to_code(operands()[2 * i + 1]));
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

  void add_catch(code_frontend_declt &&to_catch, codet &&code_catch)
  {
    add_to_operands(std::move(to_catch), std::move(code_catch));
  }

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
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
  const code_try_catcht &ret = static_cast<const code_try_catcht &>(code);
  validate_expr(ret);
  return ret;
}

inline code_try_catcht &to_code_try_catch(codet &code)
{
  PRECONDITION(code.get_statement() == ID_try_catch);
  code_try_catcht &ret = static_cast<code_try_catcht &>(code);
  validate_expr(ret);
  return ret;
}

/// This class is used to interface between a language frontend
/// and goto-convert -- it communicates the identifiers of the parameters
/// of a function or method
class code_function_bodyt : public codet
{
public:
  explicit code_function_bodyt(
    const std::vector<irep_idt> &parameter_identifiers,
    code_blockt _block)
    : codet(ID_function_body, {std::move(_block)})
  {
    set_parameter_identifiers(parameter_identifiers);
  }

  code_blockt &block()
  {
    return to_code_block(to_code(op0()));
  }

  const code_blockt &block() const
  {
    return to_code_block(to_code(op0()));
  }

  std::vector<irep_idt> get_parameter_identifiers() const;
  void set_parameter_identifiers(const std::vector<irep_idt> &);

protected:
  using codet::op0;
  using codet::op1;
  using codet::op2;
  using codet::op3;
};

inline const code_function_bodyt &to_code_function_body(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_function_body);
  DATA_INVARIANT(
    code.operands().size() == 1, "code_function_body must have one operand");
  return static_cast<const code_function_bodyt &>(code);
}

inline code_function_bodyt &to_code_function_body(codet &code)
{
  PRECONDITION(code.get_statement() == ID_function_body);
  DATA_INVARIANT(
    code.operands().size() == 1, "code_function_body must have one operand");
  return static_cast<code_function_bodyt &>(code);
}

#endif // CPROVER_UTIL_STD_CODE_H
