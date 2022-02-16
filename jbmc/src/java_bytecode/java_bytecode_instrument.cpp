/*******************************************************************\

Module: Instrument codet with assertions/runtime exceptions

Author: Cristina David

Date:   June 2017

\*******************************************************************/

#include "java_bytecode_instrument.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include "java_expr.h"
#include "java_types.h"
#include "java_utils.h"

class java_bytecode_instrumentt
{
public:
  java_bytecode_instrumentt(
    symbol_table_baset &_symbol_table,
    const bool _throw_runtime_exceptions,
    message_handlert &_message_handler)
    : symbol_table(_symbol_table),
      throw_runtime_exceptions(_throw_runtime_exceptions),
      message_handler(_message_handler)
  {
  }

  void operator()(codet &code);

protected:
  symbol_table_baset &symbol_table;
  const bool throw_runtime_exceptions;
  message_handlert &message_handler;

  code_ifthenelset throw_exception(
    const exprt &cond,
    const source_locationt &original_loc,
    const irep_idt &exc_name);

  codet check_array_access(
    const exprt &array_struct,
    const exprt &idx,
    const source_locationt &original_loc);

  codet check_arithmetic_exception(
    const exprt &denominator,
    const source_locationt &original_loc);

  codet check_null_dereference(
    const exprt &expr,
    const source_locationt &original_loc);

  code_ifthenelset check_class_cast(
    const exprt &tested_expr,
    const struct_tag_typet &target_type,
    const source_locationt &original_loc);

  codet check_array_length(
    const exprt &length,
    const source_locationt &original_loc);

  void instrument_code(codet &code);
  void add_expr_instrumentation(code_blockt &block, const exprt &expr);
  void prepend_instrumentation(codet &code, code_blockt &instrumentation);
  optionalt<codet> instrument_expr(const exprt &expr);
};

const std::vector<std::string> exception_needed_classes = {
  "java.lang.ArithmeticException",
  "java.lang.ArrayIndexOutOfBoundsException",
  "java.lang.ClassCastException",
  "java.lang.NegativeArraySizeException",
  "java.lang.NullPointerException"};

/// Creates a class stub for exc_name and generates a
///  conditional GOTO such that exc_name is thrown when
///  cond is met.
/// \param cond: condition to be met in order
///   to throw an exception
/// \param original_loc: source location in the original program
/// \param exc_name: the name of the exception to be thrown
/// \return Returns the code initialising the throwing the
///   exception
code_ifthenelset java_bytecode_instrumentt::throw_exception(
  const exprt &cond,
  const source_locationt &original_loc,
  const irep_idt &exc_name)
{
  irep_idt exc_class_name("java::"+id2string(exc_name));

  if(!symbol_table.has_symbol(exc_class_name))
  {
    generate_class_stub(
      exc_name,
      symbol_table,
      message_handler,
      struct_union_typet::componentst{});
  }

  pointer_typet exc_ptr_type = pointer_type(struct_tag_typet(exc_class_name));

  // Allocate and throw an instance of the exception class:

  symbolt &new_symbol = fresh_java_symbol(
    exc_ptr_type, "new_exception", original_loc, "new_exception", symbol_table);

  side_effect_exprt new_instance(ID_java_new, exc_ptr_type, original_loc);
  code_assignt assign_new(new_symbol.symbol_expr(), new_instance);

  side_effect_expr_throwt throw_expr(irept(), typet(), original_loc);
  throw_expr.copy_to_operands(new_symbol.symbol_expr());

  code_ifthenelset if_code(
    cond, code_blockt({assign_new, code_expressiont(throw_expr)}));

  if_code.add_source_location()=original_loc;

  return if_code;
}

/// Checks whether there is a division by zero
/// and throws ArithmeticException if necessary.
/// Exceptions are thrown when the `throw_runtime_exceptions`
/// flag is set.
/// \return Based on the value of the flag `throw_runtime_exceptions`,
///   it returns code that either throws an ArithmeticException
///   or asserts a nonzero denominator.
codet java_bytecode_instrumentt::check_arithmetic_exception(
  const exprt &denominator,
  const source_locationt &original_loc)
{
  const constant_exprt &zero=from_integer(0, denominator.type());
  const binary_relation_exprt equal_zero(denominator, ID_equal, zero);

  if(throw_runtime_exceptions)
    return throw_exception(
      equal_zero,
      original_loc,
      "java.lang.ArithmeticException");

  source_locationt assertion_loc = original_loc;
  assertion_loc.set_comment("Denominator should be nonzero");
  assertion_loc.set_property_class("integer-divide-by-zero");

  return create_fatal_assertion(
    binary_relation_exprt(denominator, ID_notequal, zero), assertion_loc);
}

/// Checks whether the array access array_struct[idx] is out-of-bounds,
/// and throws ArrayIndexOutofBoundsException/generates an assertion
/// if necessary; Exceptions are thrown when the `throw_runtime_exceptions`
/// flag is set. Otherwise, assertions are emitted.
/// \param array_struct: array being accessed
/// \param idx: index into the array
/// \param original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
///   it returns code that either throws an ArrayIndexOutPfBoundsException
///   or emits an assertion checking the array access
codet java_bytecode_instrumentt::check_array_access(
  const exprt &array_struct,
  const exprt &idx,
  const source_locationt &original_loc)
{
  const constant_exprt &zero=from_integer(0, java_int_type());
  const binary_relation_exprt ge_zero(idx, ID_ge, zero);
  const member_exprt length_field(array_struct, "length", java_int_type());
  const binary_relation_exprt lt_length(idx, ID_lt, length_field);
  const and_exprt cond(ge_zero, lt_length);

  if(throw_runtime_exceptions)
    return throw_exception(
      not_exprt(cond),
      original_loc,
      "java.lang.ArrayIndexOutOfBoundsException");

  code_blockt bounds_checks;

  source_locationt low_check_loc = original_loc;
  low_check_loc.set_comment("Array index should be >= 0");
  low_check_loc.set_property_class("array-index-out-of-bounds-low");

  source_locationt high_check_loc = original_loc;
  high_check_loc.set_comment("Array index should be < length");
  high_check_loc.set_property_class("array-index-out-of-bounds-high");

  bounds_checks.add(create_fatal_assertion(ge_zero, low_check_loc));
  bounds_checks.add(create_fatal_assertion(lt_length, high_check_loc));

  return std::move(bounds_checks);
}

/// Checks whether `class1` is an instance of `class2` and throws
/// ClassCastException/generates an assertion when necessary;
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \param tested_expr: expression to test
/// \param target_type: type to test for
/// \param original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
///   it returns code that either throws an ClassCastException or emits an
///   assertion checking the subtype relation
code_ifthenelset java_bytecode_instrumentt::check_class_cast(
  const exprt &tested_expr,
  const struct_tag_typet &target_type,
  const source_locationt &original_loc)
{
  java_instanceof_exprt class_cast_check(tested_expr, target_type);

  pointer_typet voidptr = pointer_type(java_void_type());
  exprt null_check_op = typecast_exprt::conditional_cast(tested_expr, voidptr);

  optionalt<codet> check_code;
  if(throw_runtime_exceptions)
  {
    check_code=
      throw_exception(
        not_exprt(class_cast_check),
        original_loc,
        "java.lang.ClassCastException");
  }
  else
  {
    source_locationt check_loc = original_loc;
    check_loc.set_comment("Dynamic cast check");
    check_loc.set_property_class("bad-dynamic-cast");

    codet assert_class = create_fatal_assertion(class_cast_check, check_loc);

    check_code=std::move(assert_class);
  }

  return code_ifthenelset(
    notequal_exprt(std::move(null_check_op), null_pointer_exprt(voidptr)),
    std::move(*check_code));
}

/// Checks whether \p expr is null and throws NullPointerException/
/// generates an assertion when necessary;
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \param expr: the checked expression
/// \param original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
///   it returns code that either throws an NullPointerException or emits an
///   assertion checking the subtype relation
codet java_bytecode_instrumentt::check_null_dereference(
  const exprt &expr,
  const source_locationt &original_loc)
{
  const equal_exprt equal_expr(
    expr,
    null_pointer_exprt(to_pointer_type(expr.type())));

  if(throw_runtime_exceptions)
    return throw_exception(
      equal_expr,
      original_loc, "java.lang.NullPointerException");

  source_locationt check_loc = original_loc;
  check_loc.set_comment("Null pointer check");
  check_loc.set_property_class("null-pointer-exception");

  return create_fatal_assertion(not_exprt(equal_expr), check_loc);
}

/// Checks whether \p length >= 0 and throws NegativeArraySizeException/
/// generates an assertion when necessary;
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \param length: the checked length
/// \param original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
///   it returns code that either throws an NegativeArraySizeException
///   or emits an assertion checking the subtype relation
codet java_bytecode_instrumentt::check_array_length(
  const exprt &length,
  const source_locationt &original_loc)
{
  const constant_exprt &zero=from_integer(0, java_int_type());
  const binary_relation_exprt ge_zero(length, ID_ge, zero);

  if(throw_runtime_exceptions)
    return throw_exception(
      not_exprt(ge_zero),
      original_loc,
      "java.lang.NegativeArraySizeException");

  source_locationt check_loc;
  check_loc.set_comment("Array size should be >= 0");
  check_loc.set_property_class("array-create-negative-size");

  return create_fatal_assertion(ge_zero, check_loc);
}

/// Checks whether \p expr requires instrumentation, and if so adds it
/// to \p block.
/// \param [out] block: block where instrumentation will be added
/// \param expr: expression to instrument
void java_bytecode_instrumentt::add_expr_instrumentation(
  code_blockt &block,
  const exprt &expr)
{
  if(optionalt<codet> expr_instrumentation = instrument_expr(expr))
  {
    if(expr_instrumentation->get_statement() == ID_block)
      block.append(to_code_block(*expr_instrumentation));
    else
      block.add(std::move(*expr_instrumentation));
  }
}

/// Appends \p code to \p instrumentation and overwrites reference \p code
/// with the augmented block if \p instrumentation is non-empty.
/// \param [in, out] code: code being instrumented
/// \param instrumentation: instrumentation code block to prepend
void java_bytecode_instrumentt::prepend_instrumentation(
  codet &code,
  code_blockt &instrumentation)
{
  if(instrumentation!=code_blockt())
  {
    if(code.get_statement()==ID_block)
      instrumentation.append(to_code_block(code));
    else
      instrumentation.add(code);
    code=instrumentation;
  }
}

/// Augments \p code with instrumentation in the form of either
/// assertions or runtime exceptions
/// \param code: the expression to be instrumented
void java_bytecode_instrumentt::instrument_code(codet &code)
{
  source_locationt old_source_location=code.source_location();

  const irep_idt &statement=code.get_statement();

  if(statement==ID_assign)
  {
    code_assignt code_assign=to_code_assign(code);

    code_blockt block;
    add_expr_instrumentation(block, code_assign.lhs());
    add_expr_instrumentation(block, code_assign.rhs());
    prepend_instrumentation(code, block);
  }
  else if(statement==ID_expression)
  {
    code_expressiont code_expression=
      to_code_expression(code);

    code_blockt block;
    add_expr_instrumentation(block, code_expression.expression());
    prepend_instrumentation(code, block);
  }
  else if(statement==ID_assert)
  {
    const code_assertt &code_assert=to_code_assert(code);

    // does this correspond to checkcast?
    if(code_assert.assertion().id()==ID_java_instanceof)
    {
      code_blockt block;
      const auto & instanceof
        = to_java_instanceof_expr(code_assert.assertion());

      code = check_class_cast(instanceof.tested_expr(),
                              instanceof
                                .target_type(), code_assert.source_location());
    }
  }
  else if(statement==ID_block)
  {
    Forall_operands(it, code)
      instrument_code(to_code(*it));
  }
  else if(statement==ID_label)
  {
    code_labelt &code_label=to_code_label(code);
    instrument_code(code_label.code());
  }
  else if(statement==ID_ifthenelse)
  {
    code_blockt block;
    code_ifthenelset &code_ifthenelse=to_code_ifthenelse(code);
    add_expr_instrumentation(block, code_ifthenelse.cond());
    instrument_code(code_ifthenelse.then_case());
    if(code_ifthenelse.else_case().is_not_nil())
      instrument_code(code_ifthenelse.else_case());
    prepend_instrumentation(code, block);
  }
  else if(statement==ID_switch)
  {
    code_blockt block;
    code_switcht &code_switch=to_code_switch(code);
    add_expr_instrumentation(block, code_switch.value());
    add_expr_instrumentation(block, code_switch.body());
    prepend_instrumentation(code, block);
  }
  else if(statement==ID_return)
  {
    code_blockt block;
    code_returnt &code_return = to_code_return(code);
    add_expr_instrumentation(block, code_return.return_value());
    prepend_instrumentation(code, block);
  }
  else if(statement==ID_function_call)
  {
    code_blockt block;
    code_function_callt &code_function_call=to_code_function_call(code);
    add_expr_instrumentation(block, code_function_call.lhs());
    add_expr_instrumentation(block, code_function_call.function());

    const java_method_typet &function_type =
      to_java_method_type(code_function_call.function().type());

    for(const auto &arg : code_function_call.arguments())
      add_expr_instrumentation(block, arg);

    // Check for a null this-argument of a virtual call:
    if(function_type.has_this())
    {
      block.add(check_null_dereference(
        code_function_call.arguments()[0],
        code_function_call.source_location()));
    }

    prepend_instrumentation(code, block);
  }

  // Ensure source location is retained:
  if(!old_source_location.get_line().empty())
    merge_source_location_rec(code, old_source_location);
}

/// Computes the instrumentation for \p expr in the form of
/// either assertions or runtime exceptions.
/// \param expr: the expression for which we compute instrumentation
/// \return The instrumentation for \p expr if required
optionalt<codet> java_bytecode_instrumentt::instrument_expr(const exprt &expr)
{
  code_blockt result;
  // First check our operands:
  forall_operands(it, expr)
  {
    if(optionalt<codet> op_result = instrument_expr(*it))
      result.add(std::move(*op_result));
  }

  // Add any check due at this node:
  if(expr.id()==ID_plus &&
     expr.get_bool(ID_java_array_access))
  {
    // this corresponds to ?aload and ?astore so
    // we check that 0<=index<array.length
    const plus_exprt &plus_expr=to_plus_expr(expr);
    if(plus_expr.op0().id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(plus_expr.op0());
      if(member_expr.compound().id() == ID_dereference)
      {
        const dereference_exprt &dereference_expr =
          to_dereference_expr(member_expr.compound());
        codet bounds_check=
          check_array_access(
            dereference_expr,
            plus_expr.op1(),
            expr.source_location());
        result.add(std::move(bounds_check));
      }
    }
  }
  else if(expr.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(expr);
    const irep_idt &statement=side_effect_expr.get_statement();
    if(statement==ID_throw)
    {
      // this corresponds to a throw and so we check that
      // we don't throw null
      result.add(check_null_dereference(
        to_unary_expr(expr).op(), expr.source_location()));
    }
    else if(statement==ID_java_new_array)
    {
      // this corresponds to new array so we check that
      // length is >=0
      result.add(check_array_length(
        to_multi_ary_expr(expr).op0(), expr.source_location()));
    }
  }
  else if((expr.id()==ID_div || expr.id()==ID_mod) &&
          expr.type().id()==ID_signedbv)
  {
    // check division by zero (for integer types only)
    result.add(check_arithmetic_exception(
      to_binary_expr(expr).op1(), expr.source_location()));
  }
  else if(expr.id()==ID_dereference &&
          expr.get_bool(ID_java_member_access))
  {
    // Check pointer non-null before access:
    const dereference_exprt &dereference_expr = to_dereference_expr(expr);
    codet null_dereference_check = check_null_dereference(
      dereference_expr.pointer(), dereference_expr.source_location());
    result.add(std::move(null_dereference_check));
  }

  if(result==code_blockt())
    return {};
  else
    return std::move(result);
}

/// Instruments \p code
/// \param code: the expression to be instrumented
void java_bytecode_instrumentt::operator()(codet &code)
{
  instrument_code(code);
}

/// Instruments the code attached to \p symbol with
/// runtime exceptions or corresponding assertions.
/// Exceptions are thrown when the \p throw_runtime_exceptions flag is set.
/// Otherwise, assertions are emitted.
/// \param symbol_table: global symbol table (may gain exception type stubs and
///   similar)
/// \param symbol: the symbol to instrument
/// \param throw_runtime_exceptions: flag determining whether we instrument the
///   code with runtime exceptions or with assertions. The former applies if
///   this flag is set to true.
/// \param message_handler: stream to report status and warnings
void java_bytecode_instrument_symbol(
  symbol_table_baset &symbol_table,
  symbolt &symbol,
  const bool throw_runtime_exceptions,
  message_handlert &message_handler)
{
  java_bytecode_instrumentt instrument(
    symbol_table,
    throw_runtime_exceptions,
    message_handler);
  INVARIANT(
    symbol.value.id()==ID_code,
    "java_bytecode_instrument expects a code-typed symbol but was called with"
      " " + id2string(symbol.name) + " which has a value with an id of " +
      id2string(symbol.value.id()));
  instrument(to_code(symbol.value));
}

/// Instruments the start function with an assertion that checks whether
/// an exception has escaped the entry point
/// \param init_code: the code block to which the assertion is appended
/// \param exc_symbol: the top-level exception symbol
/// \param source_location: the source location to attach to the assertion
void java_bytecode_instrument_uncaught_exceptions(
  code_blockt &init_code,
  const symbolt &exc_symbol,
  const source_locationt &source_location)
{
  // check that there is no uncaught exception
  code_assertt assert_no_exception(equal_exprt(
    exc_symbol.symbol_expr(),
    null_pointer_exprt(to_pointer_type(exc_symbol.type))));

  source_locationt assert_location = source_location;
  assert_location.set_comment("no uncaught exception");
  assert_no_exception.add_source_location() = assert_location;

  init_code.add(std::move(assert_no_exception));
}

/// Instruments all the code in the symbol_table with
/// runtime exceptions or corresponding assertions.
/// Exceptions are thrown when the \p throw_runtime_exceptions flag is set.
/// Otherwise, assertions are emitted.
/// \param symbol_table: global symbol table, all of whose code members
///   will be annotated (may gain exception type stubs and similar)
/// \param throw_runtime_exceptions: flag determining whether we instrument the
///   code with runtime exceptions or with assertions. The former applies if
///   this flag is set to true.
/// \param message_handler: stream to report status and warnings
void java_bytecode_instrument(
  symbol_tablet &symbol_table,
  const bool throw_runtime_exceptions,
  message_handlert &message_handler)
{
  java_bytecode_instrumentt instrument(
    symbol_table,
    throw_runtime_exceptions,
    message_handler);

  std::vector<irep_idt> symbols_to_instrument;
  for(const auto &symbol_pair : symbol_table.symbols)
  {
    if(symbol_pair.second.value.id() == ID_code)
    {
      symbols_to_instrument.push_back(symbol_pair.first);
    }
  }

  // instrument(...) can add symbols to the table, so it's
  // not safe to hold a reference to a symbol across a call.
  for(const auto &symbol : symbols_to_instrument)
  {
    instrument(to_code(symbol_table.get_writeable_ref(symbol).value));
  }
}
