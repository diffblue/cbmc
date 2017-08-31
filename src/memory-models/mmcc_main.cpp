/*******************************************************************\

Module: mmcc Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// mmcc Main Module

#include "mmcc_parse_options.h"

#include <util/unicode.h>

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec=narrow_argv(argc, argv_wide);
  auto narrow=to_c_str_array(std::begin(vec), std::end(vec));
  auto argv=narrow.data();
#else
int main(int argc, const char **argv)
{
#endif
  mmcc_parse_optionst parse_options(argc, argv);

  return parse_options.main();
}
