/*******************************************************************\

Module: Main Module

Author: Vincent Nimal

\*******************************************************************/

#include "musketeer_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  goto_fence_inserter_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
