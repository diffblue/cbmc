/*******************************************************************\

Module: CBMC Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Main Module

/*

  CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2014 Daniel Kroening <kroening@kroening.com>

*/

#include <util/unicode.h>

#ifdef IREP_HASH_STATS
#include <iostream>
#endif

#include "cbmc_parse_options.h"

#ifdef IREP_HASH_STATS
extern unsigned long long irep_hash_cnt;
extern unsigned long long irep_cmp_cnt;
extern unsigned long long irep_cmp_ne_cnt;
#endif

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec=narrow_argv(argc, argv_wide);
  auto argv=vec.data();
#else
int main(int argc, const char **argv)
{
#endif
  cbmc_parse_optionst parse_options(argc, argv);

  int res=parse_options.main();

  #ifdef IREP_HASH_STATS
  std::cout << "IREP_HASH_CNT=" << irep_hash_cnt << '\n';
  std::cout << "IREP_CMP_CNT=" << irep_cmp_cnt << '\n';
  std::cout << "IREP_CMP_NE_CNT=" << irep_cmp_ne_cnt << '\n';
  #endif

  return res;
}
