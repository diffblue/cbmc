/******************************************************************\

Module: symtab2gb_main

Author: Diffblue Ltd.

\******************************************************************/

/// \file
/// symtab2gb Main Module

#include "symtab2gb_parse_options.h"

int main(int argc, const char *argv[])
{
  symtab2gb_parse_optionst parse_options{argc, argv};
  return parse_options.main();
}
