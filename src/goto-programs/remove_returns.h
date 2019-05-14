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
/// `remove_returns()` does not change the signature of the function.

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H

#include <functional>

#include <util/std_code.h>
#include <util/std_types.h>

class goto_functionst;
class goto_model_functiont;
class goto_modelt;
class namespacet;
class symbol_table_baset;
class symbol_exprt;

void remove_returns(symbol_table_baset &, goto_functionst &);

typedef std::function<bool(const irep_idt &)> function_is_stubt;

void remove_returns(goto_model_functiont &, function_is_stubt);

void remove_returns(goto_modelt &);

// reverse the above operations
void restore_returns(symbol_table_baset &, goto_functionst &);

void restore_returns(goto_modelt &);

/// produces the identifier that is used to store the return
/// value of the function with the given identifier
irep_idt return_value_identifier(const irep_idt &);

/// produces the symbol that is used to store the return
/// value of the function with the given identifier
symbol_exprt return_value_symbol(const irep_idt &, const namespacet &);

/// Returns true if \p id is a special return-value symbol produced by
/// \ref return_value_identifier
bool is_return_value_identifier(const irep_idt &id);

/// Returns true if \p symbol_expr is a special return-value symbol produced by
/// \ref return_value_symbol
bool is_return_value_symbol(const symbol_exprt &symbol_expr);

/// Check if the \p function_call returns anything
/// \param function_call: the function call to be investigated
/// \return true if non-void return type and non-nil lhs
bool does_function_call_return(const code_function_callt &function_call);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_RETURNS_H
