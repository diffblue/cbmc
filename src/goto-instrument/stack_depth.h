/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

#ifndef CPROVER_STACK_DEPTH_H
#define CPROVER_STACK_DEPTH_H

class symbol_tablet;
class goto_functionst;

void stack_depth(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const int depth);

#endif
