/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_CPP_CPROVER_LIBRARY_H
#define CPROVER_CPP_CPROVER_LIBRARY_H

#include <set>

#include <util/irep.h>

class message_handlert;
class symbol_tablet;

void cprover_cpp_library_factory(
  const std::set<irep_idt> &functions,
  const symbol_tablet &,
  symbol_tablet &,
  message_handlert &);

#endif // CPROVER_CPP_CPROVER_LIBRARY_H
