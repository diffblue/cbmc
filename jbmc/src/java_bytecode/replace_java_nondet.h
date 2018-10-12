/*******************************************************************\

Module: Replace Java Nondet expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Replace Java Nondet expressions

#ifndef CPROVER_JAVA_BYTECODE_REPLACE_JAVA_NONDET_H
#define CPROVER_JAVA_BYTECODE_REPLACE_JAVA_NONDET_H

class goto_modelt;
class goto_functionst;
class goto_model_functiont;

void replace_java_nondet(goto_modelt &);

void replace_java_nondet(goto_functionst &);

void replace_java_nondet(goto_model_functiont &function);

#endif
