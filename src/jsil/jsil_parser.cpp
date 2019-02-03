/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_parser.h"

void jsil_parser_init(jsil_parsert *jsil_parser);
void jsil_scanner_init(jsil_parsert *jsil_parser);
int yyjsilparse();

bool jsil_parsert::parse()
{
  jsil_scanner_init(this);
  jsil_parser_init(this);
  return yyjsilparse()!=0;
}

void jsil_parsert::clear()
{
  parsert::clear();
  parse_tree.clear();

  // scanner state
  string_literal.clear();
  jsil_parser_init(nullptr);
  jsil_scanner_init(nullptr);
}
