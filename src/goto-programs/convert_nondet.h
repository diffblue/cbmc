/*******************************************************************\

Module: Convert side_effect_expr_nondett expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Convert side_effect_expr_nondett expressions

#ifndef CPROVER_GOTO_PROGRAMS_CONVERT_NONDET_H
#define CPROVER_GOTO_PROGRAMS_CONVERT_NONDET_H

#include <cstddef> // size_t

class goto_functionst;
class symbol_tablet;
class goto_modelt;
class message_handlert;
struct object_factory_parameterst;

/// Replace calls to nondet library functions with an internal nondet
/// representation.
/// \param goto_functions: The set of goto programs to modify.
/// \param symbol_table: The symbol table to query/update.
/// \param message_handler: For error logging.
/// \param object_factory_parameters: Parameters for the generation of nondet
///   objects.
void convert_nondet(
  goto_functionst &,
  symbol_tablet &,
  message_handlert &,
  const object_factory_parameterst &object_factory_parameters);

void convert_nondet(
  goto_modelt &,
  message_handlert &,
  const object_factory_parameterst &object_factory_parameters);

#endif
