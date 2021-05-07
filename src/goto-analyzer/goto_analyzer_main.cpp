/*******************************************************************\

Module: Goto-Analyser Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto-Analyser Main Module

#include "goto_analyzer_parse_options.h"

#ifdef _MSC_VER
#  include <util/unicode.h>

int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec=narrow_argv(argc, argv_wide);
  auto narrow=to_c_str_array(std::begin(vec), std::end(vec));
  auto argv=narrow.data();
#else
int main(int argc, const char **argv)
{
#endif
  goto_analyzer_parse_optionst parse_options(argc, argv);

  return parse_options.main();
}
