/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2005 Daniel Kroening <kroening@kroening.com>

*/

#include <util/unicode.h>

#include "parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  cbmc_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#else
int main(int argc, const char **argv)
{
  cbmc_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#endif
