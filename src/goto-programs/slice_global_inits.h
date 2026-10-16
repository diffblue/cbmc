/*******************************************************************\

Module: Remove initializations of unused global variables

Author: Daniel Poetzl

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove initializations of unused global variables

#ifndef CPROVER_GOTO_PROGRAMS_SLICE_GLOBAL_INITS_H
#define CPROVER_GOTO_PROGRAMS_SLICE_GLOBAL_INITS_H

#include <util/exception_utils.h>

class goto_modelt;
class message_handlert;

class user_input_error_exceptiont : public cprover_exception_baset
{
public:
  explicit user_input_error_exceptiont(std::string message)
    : cprover_exception_baset(std::move(message))
  {
  }
};

/// Remove initialization of global variables that are not used in any function
/// reachable from the entry point of \p goto_model.
/// Warnings are reported via \p message_handler.
void slice_global_inits(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Remove the initialization of the C++ virtual tables (symbols named
/// `virtual_table::...') that no reachable code refers to.  Unlike
/// slice_global_inits this does not require function pointers to have been
/// removed: a function is reachable if it is named (called or its address
/// taken) in reachable code or in the initializer of a global that is kept.
/// The functions named only in the removed tables are then no longer
/// address-taken, so a later function pointer removal does not consider
/// them as targets.
void slice_unused_virtual_tables(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
