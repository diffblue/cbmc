/*******************************************************************\

Module: Jsil Language Conversion

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language Conversion

#ifndef CPROVER_JSIL_JSIL_CONVERT_H
#define CPROVER_JSIL_JSIL_CONVERT_H

class jsil_parse_treet;
class message_handlert;
class symbol_tablet;

bool jsil_convert(
  const jsil_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

#endif // CPROVER_JSIL_JSIL_CONVERT_H
