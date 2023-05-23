/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_CPP_CPROVER_LIBRARY_H
#define CPROVER_CPP_CPROVER_LIBRARY_H

#include <util/symbol_table.h>

#include <set>

class message_handlert;

optionalt<symbol_tablet> cprover_cpp_library_factory(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &,
  message_handlert &);

#endif // CPROVER_CPP_CPROVER_LIBRARY_H
