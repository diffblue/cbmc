/******************************************************************\

Module: goto_harness_main

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_parse_options.h"

int main(int argc, const char *argv[])
{
  return goto_harness_parse_optionst{argc, argv}.main();
}
