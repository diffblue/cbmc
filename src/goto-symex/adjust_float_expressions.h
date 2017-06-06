/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_ADJUST_FLOAT_EXPRESSIONS_H
#define CPROVER_GOTO_SYMEX_ADJUST_FLOAT_EXPRESSIONS_H

class exprt;
class namespacet;
class goto_functionst;
class goto_modelt;

void adjust_float_expressions(
  exprt &expr,
  const namespacet &ns);

void adjust_float_expressions(
  goto_functionst &goto_functions,
  const namespacet &ns);
void adjust_float_expressions(goto_modelt &goto_model);

#endif // CPROVER_GOTO_SYMEX_ADJUST_FLOAT_EXPRESSIONS_H
