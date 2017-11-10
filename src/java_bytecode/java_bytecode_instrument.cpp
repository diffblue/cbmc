/*******************************************************************\

Module: Instrument codet with assertions/runtime exceptions

Author: Cristina David

Date:   June 2017

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/fresh_symbol.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/c_types.h>

#include <goto-programs/goto_functions.h>

#include "java_bytecode_convert_class.h"
#include "java_bytecode_instrument.h"
#include "java_entry_point.h"
#include "java_root_class.h"
#include "java_types.h"
#include "java_utils.h"

class java_bytecode_instrumentt:public messaget
{
public:
  java_bytecode_instrumentt(
    symbol_tablet &_symbol_table,
    const bool _throw_runtime_exceptions,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    throw_runtime_exceptions(_throw_runtime_exceptions),
    message_handler(_message_handler)
    {
    }

  void operator()(exprt &expr);

protected:
  symbol_tablet &symbol_table;
  const bool throw_runtime_exceptions;
  message_handlert &message_handler;

  codet throw_exception(
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

  codet check_class_cast(
    const exprt &class1,
    const exprt &class2,
    const source_locationt &original_loc);

  codet check_array_length(
    const exprt &length,
    const source_locationt &original_loc);

  void instrument_code(exprt &expr);
  void add_expr_instrumentation(code_blockt &block, const exprt &expr);
  void prepend_instrumentation(codet &code, code_blockt &instrumentation);
  codet instrument_expr(const exprt &expr);
};


/// Creates a class stub for exc_name and generates a
///  conditional GOTO such that exc_name is thrown when
///  cond is met.
/// \par parameters: `cond`: condition to be met in order
/// to throw an exception
/// `original_loc`: source location in the original program
/// `exc_name`: the name of the exception to be thrown
/// \return Returns the code initialising the throwing the
/// exception
codet java_bytecode_instrumentt::throw_exception(
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
      get_message_handler(),
      struct_union_typet::componentst{});
  }

  pointer_typet exc_ptr_type=
    pointer_type(symbol_typet(exc_class_name));

  // Allocate and throw an instance of the exception class:

  symbolt &new_symbol=
    get_fresh_aux_symbol(
      exc_ptr_type,
      "new_exception",
      "new_exception",
      original_loc,
      ID_java,
      symbol_table);

  side_effect_exprt new_instance(ID_java_new, exc_ptr_type);
  code_assignt assign_new(new_symbol.symbol_expr(), new_instance);

  side_effect_expr_throwt throw_expr;
  throw_expr.copy_to_operands(new_symbol.symbol_expr());

  code_blockt throw_code;
  throw_code.move_to_operands(assign_new);
  throw_code.copy_to_operands(code_expressiont(throw_expr));

  code_ifthenelset if_code;
  if_code.add_source_location()=original_loc;
  if_code.cond()=cond;
  if_code.then_case()=throw_code;

  return if_code;
}


/// Checks whether there is a division by zero
/// and throws ArithmeticException if necessary.
/// Exceptions are thrown when the `throw_runtime_exceptions`
/// flag is set.
/// \return Based on the value of the flag `throw_runtime_exceptions`,
/// it returns code that either throws an ArithmeticException
/// or asserts a nonzero denominator.
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

  code_assertt ret(binary_relation_exprt(denominator, ID_notequal, zero));
  ret.add_source_location()=original_loc;
  ret.add_source_location().set_comment("Denominator should be nonzero");
  ret.add_source_location().set_property_class("integer-divide-by-zero");
  return ret;
}

/// Checks whether the array access array_struct[idx] is out-of-bounds,
/// and throws ArrayIndexOutofBoundsException/generates an assertion
/// if necessary; Exceptions are thrown when the `throw_runtime_exceptions`
/// flag is set. Otherwise, assertions are emitted.
/// \par parameters: `array_struct`: the array being accessed
/// `idx`: index into the array
/// `original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
/// it returns code that either throws an ArrayIndexOutPfBoundsException
/// or emits an assertion checking the array access
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
  bounds_checks.add(code_assertt(ge_zero));
  bounds_checks.operands().back().add_source_location()=original_loc;
  bounds_checks.operands().back().add_source_location()
    .set_comment("Array index should be >= 0");
  bounds_checks.operands().back().add_source_location()
    .set_property_class("array-index-out-of-bounds-low");

  bounds_checks.add(code_assertt(lt_length));
  bounds_checks.operands().back().add_source_location()=original_loc;
  bounds_checks.operands().back().add_source_location()
    .set_comment("Array index should be < length");
  bounds_checks.operands().back().add_source_location()
    .set_property_class("array-index-out-of-bounds-high");

  return bounds_checks;
}

/// Checks whether `class1` is an instance of `class2` and throws
/// ClassCastException/generates an assertion when necessary;
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \par parameters: `class1`: the subclass
/// `class2`: the super class
/// `original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
/// it returns code that either throws an ClassCastException or emits an
/// assertion checking the subtype relation
codet java_bytecode_instrumentt::check_class_cast(
  const exprt &class1,
  const exprt &class2,
  const source_locationt &original_loc)
{
  binary_predicate_exprt class_cast_check(
    class1, ID_java_instanceof, class2);

  pointer_typet voidptr=pointer_type(empty_typet());
  exprt null_check_op=class1;
  if(null_check_op.type()!=voidptr)
    null_check_op.make_typecast(voidptr);

  codet check_code;
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
    code_assertt assert_class(class_cast_check);
    assert_class.add_source_location().
      set_comment("Dynamic cast check");
    assert_class.add_source_location().
      set_property_class("bad-dynamic-cast");
    check_code=std::move(assert_class);
  }

  code_ifthenelset conditional_check;
  notequal_exprt op_not_null(null_check_op, null_pointer_exprt(voidptr));
  conditional_check.cond()=std::move(op_not_null);
  conditional_check.then_case()=std::move(check_code);
  return conditional_check;
}

/// Checks whether `expr` is null and throws NullPointerException/
/// generates an assertion when necessary;
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \par parameters: `expr`: the checked expression
/// `original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
/// it returns code that either throws an NullPointerException or emits an
/// assertion checking the subtype relation
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

  code_assertt check((not_exprt(equal_expr)));
  check.add_source_location()
    .set_comment("Throw null");
  check.add_source_location()
    .set_property_class("null-pointer-exception");
  return check;
}

/// Checks whether `length`>=0 and throws NegativeArraySizeException/
/// generates an assertion when necessary;
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \par parameters: `length`: the checked length
/// `original_loc: source location in the original code
/// \return Based on the value of the flag `throw_runtime_exceptions`,
/// it returns code that either throws an NegativeArraySizeException
/// or emits an assertion checking the subtype relation
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

  code_assertt check(ge_zero);
  check.add_source_location().set_comment("Array size should be >= 0");
  check.add_source_location()
    .set_property_class("array-create-negative-size");
  return check;
}

/// Checks whether `expr` requires instrumentation, and if so adds it
/// to `block`.
/// \param [out] block: block where instrumentation will be added
/// \param expr: expression to instrument
void java_bytecode_instrumentt::add_expr_instrumentation(
  code_blockt &block,
  const exprt &expr)
{
  codet expr_instrumentation=instrument_expr(expr);
  if(expr_instrumentation!=code_skipt())
  {
    if(expr_instrumentation.get_statement()==ID_block)
      block.append(to_code_block(expr_instrumentation));
    else
      block.move_to_operands(expr_instrumentation);
  }
}

/// Appends `code` to `instrumentation` and overwrites reference `code`
/// with the augmented block if `instrumentation` is non-empty.
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
      instrumentation.copy_to_operands(code);
    code=instrumentation;
  }
}

/// Augments `expr` with instrumentation in the form of either
/// assertions or runtime exceptions
/// \par parameters: `expr`: the expression to be instrumented
void java_bytecode_instrumentt::instrument_code(exprt &expr)
{
  codet &code=to_code(expr);
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

      INVARIANT(
        code_assert.assertion().operands().size()==2,
        "Instanceof should have 2 operands");

      code=
        check_class_cast(
          code_assert.assertion().op0(),
          code_assert.assertion().op1(),
          code_assert.source_location());
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
    if(code.operands().size()==1)
    {
      code_blockt block;
      add_expr_instrumentation(block, code.op0());
      prepend_instrumentation(code, block);
    }
  }
  else if(statement==ID_function_call)
  {
    code_blockt block;
    code_function_callt &code_function_call=to_code_function_call(code);
    add_expr_instrumentation(block, code_function_call.lhs());
    add_expr_instrumentation(block, code_function_call.function());

    const code_typet &function_type=
      to_code_type(code_function_call.function().type());

    // Check for a null this-argument of a virtual call:
    if(function_type.has_this())
    {
      block.copy_to_operands(
        check_null_dereference(
          code_function_call.arguments()[0],
          code_function_call.source_location()));
    }

    for(const auto &arg : code_function_call.arguments())
      add_expr_instrumentation(block, arg);

    prepend_instrumentation(code, block);
  }

  // Ensure source location is retained:
  if(!old_source_location.get_line().empty())
    merge_source_location_rec(code, old_source_location);
}

/// Computes the instrumentation for `expr` in the form of
/// either assertions or runtime exceptions.
/// \par parameters: `expr`: the expression for which we compute
/// instrumentation
/// \return: The instrumentation required for `expr`
codet java_bytecode_instrumentt::instrument_expr(
  const exprt &expr)
{
  code_blockt result;
  // First check our operands:
  forall_operands(it, expr)
  {
    codet op_result=instrument_expr(*it);
    if(op_result!=code_skipt())
      result.move_to_operands(op_result);
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
      if(member_expr.op0().id()==ID_dereference)
      {
        const dereference_exprt &dereference_expr=
          to_dereference_expr(member_expr.op0());
        codet bounds_check=
          check_array_access(
            dereference_expr,
            plus_expr.op1(),
            expr.source_location());
        result.move_to_operands(bounds_check);
      }
    }
  }
  else if(expr.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(expr);
    const irep_idt &statement=side_effect_expr.get_statement();
    if(statement==ID_throw)
    {
      // this corresponds to athrow and so we check that
      // we don't throw null
      result.copy_to_operands(
        check_null_dereference(
          expr.op0(),
          expr.source_location()));
    }
    else if(statement==ID_java_new_array)
    {
      // this correpond to new array so we check that
      // length is >=0
      result.copy_to_operands(
        check_array_length(
          expr.op0(),
          expr.source_location()));
    }
  }
  else if((expr.id()==ID_div || expr.id()==ID_mod) &&
          expr.type().id()==ID_signedbv)
  {
    // check division by zero (for integer types only)
    result.copy_to_operands(
      check_arithmetic_exception(
        expr.op1(),
        expr.source_location()));
  }
  else if(expr.id()==ID_dereference &&
          expr.get_bool(ID_java_member_access))
  {
    // Check pointer non-null before access:
    const dereference_exprt dereference_expr=to_dereference_expr(expr);
    codet null_dereference_check=
      check_null_dereference(
        dereference_expr.op0(),
        dereference_expr.source_location());
    result.move_to_operands(null_dereference_check);
  }

  if(result==code_blockt())
    return code_skipt();
  else
    return result;
}

/// Instruments `expr`
/// \par parameters: `expr`: the expression to be instrumented
void java_bytecode_instrumentt::operator()(exprt &expr)
{
  instrument_code(expr);
}

/// Instruments the code attached to `symbol` with
/// runtime exceptions or corresponding assertions.
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
/// Otherwise, assertions are emitted.
/// \param symbol_table: global symbol table (may gain exception type stubs and
///   similar)
/// \param symbol: the symbol to instrument
/// \param throw_runtime_exceptions: flag determining whether we instrument the
///   code with runtime exceptions or with assertions. The former applies if
///   this flag is set to true.
/// \param message_handler: stream to report status and warnings
void java_bytecode_instrument_symbol(
  symbol_tablet &symbol_table,
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
    "java_bytecode_instrument expects a code-typed symbol");
  instrument(symbol.value);
}

/// Instruments all the code in the symbol_table with
/// runtime exceptions or corresponding assertions.
/// Exceptions are thrown when the `throw_runtime_exceptions` flag is set.
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
  forall_symbols(s_it, symbol_table.symbols)
  {
    if(s_it->second.value.id()==ID_code)
      symbols_to_instrument.push_back(s_it->first);
  }

  // instrument(...) can add symbols to the table, so it's
  // not safe to hold a reference to a symbol across a call.
  for(const auto &symbol : symbols_to_instrument)
    instrument(symbol_table.get_writeable_ref(symbol).value);
}
