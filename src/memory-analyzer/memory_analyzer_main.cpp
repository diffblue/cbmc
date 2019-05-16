/*******************************************************************\

Module: Symbol Analyzer

Author: Malte Mues <mail.mues@gmail.com>

\*******************************************************************/

/// \file
/// Memory analyzer interface

#include "memory_analyzer_parse_options.h"

int main(int argc, const char **argv)
{
  memory_analyzer_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
