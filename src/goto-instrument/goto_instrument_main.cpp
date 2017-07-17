/*******************************************************************\

Module: Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Main Module

#include "goto_instrument_parse_options.h"

#include <util/unicode.h>

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
#else
int main(int argc, const char **argv)
{
#endif
  goto_instrument_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
