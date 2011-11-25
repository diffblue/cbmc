/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

#ifndef CPROVER_STACK_DEPTH_H
#define CPROVER_STACK_DEPTH_H

class contextt;
class goto_functionst;

void stack_depth(
  contextt &context,
  goto_functionst &goto_functions,
  const int depth);

#endif
