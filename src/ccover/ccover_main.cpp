/*******************************************************************\

Module: ccover Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ccover Main Module

/*

  ccover
  Test suite generation for ANSI-C
  Copyright (C) 2018 Daniel Kroening <kroening@kroening.com>

*/

#include "ccover_parse_options.h"

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
  ccover_parse_optionst parse_options(argc, argv);

  int res=parse_options.main();

  return res;
}
