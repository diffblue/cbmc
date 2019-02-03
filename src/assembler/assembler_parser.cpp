/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "assembler_parser.h"

int yyassemblerlex();
void assembler_scanner_init(assembler_parsert *assembler_parser);

bool assembler_parsert::parse()
{
  assembler_scanner_init(this);
  yyassemblerlex();
  return false;
}

void assembler_parsert::clear()
{
  parsert::clear();
  instructions.clear();
  assembler_scanner_init(nullptr);
}
