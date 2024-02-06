/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "assembler_parser.h"

char *yyassemblerget_text(void *);

int yyassemblererror(
  assembler_parsert &assembler_parser,
  void *scanner,
  const std::string &error)
{
  assembler_parser.parse_error(error, yyassemblerget_text(scanner));
  return 0;
}

int yyassemblerlex_init_extra(assembler_parsert *, void **);
int yyassemblerlex(void *);
int yyassemblerlex_destroy(void *);

bool assembler_parsert::parse()
{
  void *scanner;
  yyassemblerlex_init_extra(this, &scanner);
  yyassemblerlex(scanner);
  yyassemblerlex_destroy(scanner);
  return false;
}
