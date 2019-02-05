/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

/// \file
/// Replace function returns by assignments to global variables

/// The functions `remove_returns()` remove return instructions from a goto
/// program. The `restore_returns()` functions restore the returns in a goto
/// program in which they have been removed previously.
///
/// In a goto program in which returns have not been removed, functions return
/// values via the `return` instruction, which is followed by a `GOTO` to the
/// end of the function. Unlike in C, in a goto program the `return` instruction
/// does not cause control-flow to return to the call site. Instead, it simply
/// sets the return value that will be returned once the function returns to the
/// call site when the `END_FUNCTION` instruction is encountered.
///
/// Consider the following C code (with ... indicating further code):
///
/// ```
/// int func()
/// {
///   ...
///   return 1;
///   ...
/// }
///
/// r = func();
///
/// ```
///
/// This code would appear in a goto program as follows:
///
/// ```
/// func
///    ...
///    return 1;
///    GOTO 1
///    ...
/// 1: END_FUNCTION
///
/// r = func();
/// ```
///
/// The return removal pass introduces a thread-local global variable
/// `func#return_value` (one for each non-void function) to which the return
/// value is assigned, and this variable is then assigned to the lhs expression
/// that takes the function return value:
///
/// ```
/// func
///    ...
///    func#return_value = 1;
///    GOTO 1
///    ...
/// 1: END_FUNCTION
///
/// func();
/// r = func#return_value;
///
/// ```
///
/// As `return` instructions are removed, the return types of the function types
/// are set to void as well (represented by the type `empty_typet`). This
/// applies both to the functions (i.e., the member `type` of `goto_functiont`)
/// and to the call sites (i.e., the type
/// `to_code_function_call(code).function().type()` with `code` being the code
/// member of the `instructiont` instance that represents the function call).
///
/// The types of function pointer expressions in the goto program are however
/// not changed. For example, in an assignment where `func` is assigned to a
/// function pointer, such as `int (*f)(void) = func`, the function types
/// appearing in the lhs and rhs both retain the integer return type.

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H

#include <functional>

#include <util/std_types.h>

#define RETURN_VALUE_SUFFIX "#return_value"

class goto_functionst;
class goto_model_functiont;
class goto_modelt;
class symbol_table_baset;

void remove_returns(symbol_table_baset &, goto_functionst &);

typedef std::function<bool(const irep_idt &)> function_is_stubt;

void remove_returns(goto_model_functiont &, function_is_stubt);

void remove_returns(goto_modelt &);

// reverse the above operations
void restore_returns(symbol_table_baset &, goto_functionst &);

void restore_returns(goto_modelt &);

code_typet original_return_type(
  const symbol_table_baset &symbol_table,
  const irep_idt &function_id);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
