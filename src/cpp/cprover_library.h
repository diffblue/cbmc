/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_CPP_CPROVER_LIBRARY_H
#define CPROVER_CPP_CPROVER_LIBRARY_H

#include <set>

#include <util/irep.h>

class message_handlert;
class symbol_table_baset;

void cprover_cpp_library_factory(
  const std::set<irep_idt> &functions,
  const symbol_table_baset &,
  symbol_table_baset &,
  message_handlert &);

#endif // CPROVER_CPP_CPROVER_LIBRARY_H
