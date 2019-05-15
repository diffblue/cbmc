/******************************************************************\

Module: symtab2gb_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_SYMTAB2GB_SYMTAB2GB_PARSE_OPTIONS_H
#define CPROVER_SYMTAB2GB_SYMTAB2GB_PARSE_OPTIONS_H

#include <util/parse_options.h>

#define SYMTAB2GB_OUT_FILE_OPT "out"

// clang-format off

#define SYMTAB2GB_OPTIONS                                                      \
  "(" SYMTAB2GB_OUT_FILE_OPT "):"                                              \
// end options

// clang-format on

class symtab2gb_parse_optionst : public parse_options_baset
{
public:
  symtab2gb_parse_optionst(int argc, const char *argv[]);
  void help() override;
  int doit() override;
};

#endif // CPROVER_SYMTAB2GB_SYMTAB2GB_PARSE_OPTIONS_H
