/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#include "jsil_parser.h"

jsil_parsert jsil_parser;

/*******************************************************************\

Function: yyjsilerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extern char *yyjsiltext;

int yyjsilerror(const std::string &error)
{
  jsil_parser.parse_error(error, yyjsiltext);
  return 0;
}
