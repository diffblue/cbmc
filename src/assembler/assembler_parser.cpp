/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "assembler_parser.h"

assembler_parsert assembler_parser;

/*******************************************************************\

Function: yyassemblererror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extern char *yyassemblertext;

int yyassemblererror(const std::string &error)
{
  assembler_parser.parse_error(error, yyassemblertext);
  return 0;
}

