/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_parser.h"

jsil_parsert jsil_parser;

extern char *yyjsiltext;

int yyjsilerror(const std::string &error)
{
  jsil_parser.parse_error(error, yyjsiltext);
  return 0;
}
