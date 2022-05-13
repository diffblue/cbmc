/*******************************************************************\

Module: Data structures representing instructions in a GOTO program

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_UTIL_GOTO_INSTRUCTION_CODE_H
#define CPROVER_UTIL_GOTO_INSTRUCTION_CODE_H

#include <util/cprover_prefix.h>
#include <util/std_code_base.h>
#include <util/std_expr.h>

using goto_instruction_codet = codet;

/// A \ref goto_instruction_codet representing an assignment in the program.
/// For example, if an expression `e1` is represented as an \ref exprt `expr1`
/// and an expression `e2` is represented as an \ref exprt `expr2`, the
/// assignment `e1 = e2;` can be represented as `code_assignt(expr1, expr2)`.
class code_assignt : public goto_instruction_codet
{
public:
  code_assignt() : goto_instruction_codet(ID_assign)
  {
    operands().resize(2);
  }

  code_assignt(exprt lhs, exprt rhs)
    : goto_instruction_codet(ID_assign, {std::move(lhs), std::move(rhs)})
  {
  }

  code_assignt(exprt lhs, exprt rhs, source_locationt loc)
    : goto_instruction_codet(
        ID_assign,
        {std::move(lhs), std::move(rhs)},
        std::move(loc))
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
    const goto_instruction_codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, code.operands().size() == 2, "assignment must have two operands");
  }

  static void validate(
    const goto_instruction_codet &code,
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
    const goto_instruction_codet &code,
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
  using goto_instruction_codet::op0;
  using goto_instruction_codet::op1;
  using goto_instruction_codet::op2;
  using goto_instruction_codet::op3;
};

template <>
inline bool can_cast_expr<code_assignt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_assign);
}

inline void validate_expr(const code_assignt &x)
{
  code_assignt::check(x);
}

inline const code_assignt &to_code_assign(const goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_assign);
  code_assignt::check(code);
  return static_cast<const code_assignt &>(code);
}

inline code_assignt &to_code_assign(goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_assign);
  code_assignt::check(code);
  return static_cast<code_assignt &>(code);
}

/// A \ref goto_instruction_codet representing the removal of
/// a local variable going out of scope.
class code_deadt : public goto_instruction_codet
{
public:
  explicit code_deadt(symbol_exprt symbol)
    : goto_instruction_codet(ID_dead, {std::move(symbol)})
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

  static void check(
    const goto_instruction_codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      code.operands().size() == 1,
      "removal (code_deadt) must have one operand");
    DATA_CHECK(
      vm,
      code.op0().id() == ID_symbol,
      "removing a non-symbol: " + id2string(code.op0().id()) + "from scope");
  }

protected:
  using goto_instruction_codet::op0;
  using goto_instruction_codet::op1;
  using goto_instruction_codet::op2;
  using goto_instruction_codet::op3;
};

template <>
inline bool can_cast_expr<code_deadt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_dead);
}

inline void validate_expr(const code_deadt &x)
{
  code_deadt::check(x);
}

inline const code_deadt &to_code_dead(const goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_dead);
  code_deadt::check(code);
  return static_cast<const code_deadt &>(code);
}

inline code_deadt &to_code_dead(goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_dead);
  code_deadt::check(code);
  return static_cast<code_deadt &>(code);
}

/// A `goto_instruction_codet` representing the declaration of a local variable.
/// For example, if a variable (symbol) `x` is represented as a
/// \ref symbol_exprt `sym`, then the declaration of this variable can be
/// represented as `code_declt(sym)`.
class code_declt : public goto_instruction_codet
{
public:
  explicit code_declt(symbol_exprt symbol)
    : goto_instruction_codet(ID_decl, {std::move(symbol)})
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

  static void check(
    const goto_instruction_codet &code,
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

template <>
inline bool can_cast_expr<code_declt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_decl);
}

inline void validate_expr(const code_declt &x)
{
  code_declt::check(x);
}

inline const code_declt &to_code_decl(const goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_decl);
  code_declt::check(code);
  return static_cast<const code_declt &>(code);
}

inline code_declt &to_code_decl(goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_decl);
  code_declt::check(code);
  return static_cast<code_declt &>(code);
}

/// \ref goto_instruction_codet representation of a function call statement.
/// The function call statement has three operands.
/// The first is the expression that is used to store the return value.
/// The second is the function called.
/// The third is a vector of argument values.
class code_function_callt : public goto_instruction_codet
{
public:
  explicit code_function_callt(exprt _function)
    : goto_instruction_codet(
        ID_function_call,
        {nil_exprt(), std::move(_function), exprt(ID_arguments)})
  {
  }

  typedef exprt::operandst argumentst;

  code_function_callt(exprt _lhs, exprt _function, argumentst _arguments)
    : goto_instruction_codet(
        ID_function_call,
        {std::move(_lhs), std::move(_function), exprt(ID_arguments)})
  {
    arguments() = std::move(_arguments);
  }

  code_function_callt(exprt _function, argumentst _arguments)
    : code_function_callt(std::move(_function))
  {
    arguments() = std::move(_arguments);
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
    const goto_instruction_codet &code,
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
    const goto_instruction_codet &code,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(code, vm);

    if(code.op0().id() != ID_nil)
      DATA_CHECK(
        vm,
        code.op0().type() == to_code_type(code.op1().type()).return_type(),
        "function returns expression of wrong type");
  }

  static void validate_full(
    const goto_instruction_codet &code,
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
  using goto_instruction_codet::op0;
  using goto_instruction_codet::op1;
  using goto_instruction_codet::op2;
  using goto_instruction_codet::op3;
};

template <>
inline bool can_cast_expr<code_function_callt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_function_call);
}

inline void validate_expr(const code_function_callt &x)
{
  code_function_callt::check(x);
}

inline const code_function_callt &
to_code_function_call(const goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_function_call);
  code_function_callt::check(code);
  return static_cast<const code_function_callt &>(code);
}

inline code_function_callt &to_code_function_call(goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_function_call);
  code_function_callt::check(code);
  return static_cast<code_function_callt &>(code);
}

/// A `goto_instruction_codet` representing the declaration that an input of
/// a particular description has a value which corresponds to the value of a
/// given expression (or expressions).
/// When working with the C front end, calls to the `__CPROVER_input` intrinsic
/// can be added to the input code in order add instructions of this type to the
/// goto program.
/// The first argument is expected to be a C string denoting the input
/// identifier. The second argument is the expression for the input value.
class code_inputt : public goto_instruction_codet
{
public:
  /// This constructor is for support of calls to `__CPROVER_input` in user
  /// code. Where the first first argument is a description which may be any
  /// `const char *` and one or more corresponding expression arguments follow.
  explicit code_inputt(
    std::vector<exprt> arguments,
    optionalt<source_locationt> location = {});

  /// This constructor is intended for generating input instructions as part of
  /// synthetic entry point code, rather than as part of user code.
  /// \param description: This is used to construct an expression for a pointer
  ///   to a string constant containing the description text. This expression
  ///   is then used as the first argument.
  /// \param expression: This expression corresponds to a value which should be
  ///   recorded as an input.
  /// \param location: A location to associate with this instruction.
  code_inputt(
    const irep_idt &description,
    exprt expression,
    optionalt<source_locationt> location = {});

  static void check(
    const goto_instruction_codet &code,
    const validation_modet vm = validation_modet::INVARIANT);
};

template <>
inline bool can_cast_expr<code_inputt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_input);
}

inline void validate_expr(const code_inputt &input)
{
  code_inputt::check(input);
}

/// A `goto_instruction_codet` representing the declaration that an output of
/// a particular description has a value which corresponds to the value of a
/// given expression (or expressions).
/// When working with the C front end, calls to the `__CPROVER_output` intrinsic
/// can be added to the input code in order add instructions of this type to the
/// goto program.
/// The first argument is expected to be a C string denoting the output
/// identifier. The second argument is the expression for the output value.
class code_outputt : public goto_instruction_codet
{
public:
  /// This constructor is for support of calls to `__CPROVER_output` in user
  /// code. Where the first first argument is a description which may be any
  /// `const char *` and one or more corresponding expression arguments follow.
  explicit code_outputt(
    std::vector<exprt> arguments,
    optionalt<source_locationt> location = {});

  /// This constructor is intended for generating output instructions as part of
  /// synthetic entry point code, rather than as part of user code.
  /// \param description: This is used to construct an expression for a pointer
  ///   to a string constant containing the description text.
  /// \param expression: This expression corresponds to a value which should be
  ///   recorded as an output.
  /// \param location: A location to associate with this instruction.
  code_outputt(
    const irep_idt &description,
    exprt expression,
    optionalt<source_locationt> location = {});

  static void check(
    const goto_instruction_codet &code,
    const validation_modet vm = validation_modet::INVARIANT);
};

template <>
inline bool can_cast_expr<code_outputt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_output);
}

inline void validate_expr(const code_outputt &output)
{
  code_outputt::check(output);
}

/// \ref goto_instruction_codet representation of a "return from a
/// function" statement.
class code_returnt : public goto_instruction_codet
{
public:
  explicit code_returnt(exprt _op)
    : goto_instruction_codet(ID_return, {std::move(_op)})
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

  static void check(
    const goto_instruction_codet &code,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(vm, code.operands().size() == 1, "return must have one operand");
  }

protected:
  using goto_instruction_codet::op0;
  using goto_instruction_codet::op1;
  using goto_instruction_codet::op2;
  using goto_instruction_codet::op3;
};

template <>
inline bool can_cast_expr<code_returnt>(const exprt &base)
{
  return detail::can_cast_code_impl(base, ID_return);
}

inline void validate_expr(const code_returnt &x)
{
  code_returnt::check(x);
}

inline const code_returnt &to_code_return(const goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_return);
  code_returnt::check(code);
  return static_cast<const code_returnt &>(code);
}

inline code_returnt &to_code_return(goto_instruction_codet &code)
{
  PRECONDITION(code.get_statement() == ID_return);
  code_returnt::check(code);
  return static_cast<code_returnt &>(code);
}

/// \brief Builds a \ref code_function_callt
/// to `__CPROVER_havoc_slice(p, size)`.
///
/// \param p The pointer argument.
/// \param size The size argument.
/// \param ns Namespace where the `__CPROVER_havoc_slice symbol` can be found.
/// \remarks: It is a PRECONDITION that `__CPROVER_havoc_slice` exists
///   in the namespace
///
/// \return A \ref code_function_callt expression
///         `nil_exprt() := __CPROVER_havoc_slice(p, size)`.
inline code_function_callt
havoc_slice_call(const exprt &p, const exprt &size, const namespacet &ns);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_INSTRUCTION_CODE_H
