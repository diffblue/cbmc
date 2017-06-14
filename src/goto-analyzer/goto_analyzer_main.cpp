/*******************************************************************\

Module: Goto-Analyser Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto-Analyser Main Module

#include <util/unicode.h>

#include "goto_analyzer_parse_options.h"

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
#else
int main(int argc, const char **argv)
{
#endif
  goto_analyzer_parse_optionst parse_options(argc, argv);

  return parse_options.main();
}
