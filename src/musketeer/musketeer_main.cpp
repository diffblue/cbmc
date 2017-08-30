/*******************************************************************\

Module: Main Module

Author: Vincent Nimal

\*******************************************************************/

/// \file
/// Main Module

#include "musketeer_parse_options.h"

int main(int argc, const char **argv)
{
  goto_fence_inserter_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
