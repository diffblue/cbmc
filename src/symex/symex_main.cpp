/*******************************************************************\

Module: Symex Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symex Main Module

#include <util/unicode.h>

#include "symex_parse_options.h"

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  symex_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
#else
int main(int argc, const char **argv)
{
  symex_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
#endif
