/*******************************************************************\

Module: CBMC Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Main Module

/*

  JBMC
  Bounded Model Checking for Java
  Copyright (C) 2017-2018 Daniel Kroening <kroening@kroening.com>

*/

#include "jbmc_parse_options.h"

#include <util/unicode.h>

#ifdef IREP_HASH_STATS
#include <iostream>
#endif

#ifdef IREP_HASH_STATS
extern unsigned long long irep_hash_cnt;
extern unsigned long long irep_cmp_cnt;
extern unsigned long long irep_cmp_ne_cnt;
#endif

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
  jbmc_parse_optionst parse_options(argc, argv);

  int res=parse_options.main();

  #ifdef IREP_HASH_STATS
  std::cout << "IREP_HASH_CNT=" << irep_hash_cnt << '\n';
  std::cout << "IREP_CMP_CNT=" << irep_cmp_cnt << '\n';
  std::cout << "IREP_CMP_NE_CNT=" << irep_cmp_ne_cnt << '\n';
  #endif

  return res;
}
