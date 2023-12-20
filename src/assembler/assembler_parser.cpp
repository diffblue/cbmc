/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "assembler_parser.h"

extern char *yyassemblertext;

int yyassemblererror(
  assembler_parsert &assembler_parser,
  const std::string &error)
{
  assembler_parser.parse_error(error, yyassemblertext);
  return 0;
}
