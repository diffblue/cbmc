/*******************************************************************\

Module: Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Main Module

#include <util/unicode.h>

#include "goto_instrument_parse_options.h"

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec=narrow_argv(argc, argv_wide);
  auto argv=vec.data();
#else
int main(int argc, const char **argv)
{
#endif
  goto_instrument_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
