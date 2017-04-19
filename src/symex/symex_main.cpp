/*******************************************************************\

Module: Symex Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/unicode.h>

#include "symex_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec=narrow_argv(argc, argv_wide);
  auto argv=vec.data();
#else
int main(int argc, const char **argv)
{
#endif
  symex_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
