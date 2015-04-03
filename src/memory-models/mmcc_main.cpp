/*******************************************************************\

Module: mmcc Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/unicode.h>

#include "mmcc_parse_options.h"

/*******************************************************************\

Function: main / wmain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
#else
int main(int argc, const char **argv)
{
#endif
  mmcc_parse_optionst parse_options(argc, argv);

  return parse_options.main();
}
