/******************************************************************\

Module: goto_harness_main

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_parse_options.h"

int main(int argc, const char *argv[])
{
  auto parse_options = goto_harness_parse_optionst(argc, argv);
  return parse_options.main();
}
