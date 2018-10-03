/*******************************************************************\

Module: Convert side_effect_expr_nondett expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Convert side_effect_expr_nondett expressions using java_object_factory

#ifndef CPROVER_JAVA_BYTECODE_CONVERT_NONDET_H
#define CPROVER_JAVA_BYTECODE_CONVERT_NONDET_H

#include <cstddef> // size_t
#include <util/irep.h>

class goto_functionst;
class symbol_table_baset;
class goto_modelt;
class goto_model_functiont;
class message_handlert;
struct object_factory_parameterst;

/// Converts side_effect_exprt_nondett expressions using java_object_factory.
/// For example, NONDET(SomeClass *) may become a nondet choice between a null
/// pointer and a fresh instance of SomeClass, whose fields are in turn nondet
/// initialized in the same way. See \ref java_object_factory.h for details.
///
/// Note the code introduced has been freshly `goto_convert`'d without any
/// passes such as \ref remove_java_new being run. Therefore the caller may need
/// to (re-)run this and other expected GOTO transformations after this pass
/// completes.
/// \param goto_functions: The set of goto programs to modify.
/// \param symbol_table: The symbol table to query/update.
/// \param message_handler: For error logging.
/// \param object_factory_parameters: Parameters for the generation of nondet
///   objects.
void convert_nondet(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const object_factory_parameterst &object_factory_parameters);

void convert_nondet(
  goto_modelt &,
  message_handlert &,
  const object_factory_parameterst &object_factory_parameters);

/// Converts side_effect_exprt_nondett expressions using java_object_factory.
/// For example, NONDET(SomeClass *) may become a nondet choice between a null
/// pointer and a fresh instance of SomeClass, whose fields are in turn nondet
/// initialized in the same way. See \ref java_object_factory.h for details.
///
/// Note the code introduced has been freshly `goto_convert`'d without any
/// passes such as \ref remove_java_new being run. Therefore the caller may need
/// to (re-)run this and other expected GOTO transformations after this pass
/// completes.
/// \param function: goto program to modify
/// \param message_handler: For error logging.
/// \param object_factory_parameters: Parameters for the generation of nondet
///   objects.
/// \param mode: Mode for newly created symbols
void convert_nondet(
  goto_model_functiont &function,
  message_handlert &message_handler,
  const object_factory_parameterst &object_factory_parameters,
  const irep_idt &mode);

#endif // CPROVER_JAVA_BYTECODE_CONVERT_NONDET_H
