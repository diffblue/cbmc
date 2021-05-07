/*******************************************************************\

Module: Handling of functions without body

Author: Michael Tautschnig

Date: July 2016

\*******************************************************************/

/// \file
/// Handling of functions without body

#ifndef CPROVER_UNDEFINED_FUNCTIONS_H
#define CPROVER_UNDEFINED_FUNCTIONS_H

#include <iosfwd>

class goto_modelt;

void list_undefined_functions(
  const goto_modelt &,
  std::ostream &);

void undefined_function_abort_path(goto_modelt &);

#endif
