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

/// Replace calls to nondet library functions with an internal nondet
/// representation.
/// \param goto_model: The goto program to modify.
void replace_java_nondet(goto_modelt &);

void replace_java_nondet(goto_functionst &);

/// Replace calls to nondet library functions with an internal nondet
/// representation in a single function.
/// \param function: The goto program to modify.
void replace_java_nondet(goto_model_functiont &function);

#endif // CPROVER_JAVA_BYTECODE_REPLACE_JAVA_NONDET_H
