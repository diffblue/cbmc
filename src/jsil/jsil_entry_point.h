/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#ifndef CPROVER_JSIL_JSIL_ENTRY_POINT_H
#define CPROVER_JSIL_JSIL_ENTRY_POINT_H

class message_handlert;
class symbol_tablet;

bool jsil_entry_point(
  class symbol_tablet &symbol_table,
  class message_handlert &message_handler);

#endif // CPROVER_JSIL_JSIL_ENTRY_POINT_H
