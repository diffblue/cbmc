/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2005 Daniel Kroening <kroening@kroening.com>

*/

#include <cstdlib>
#include <csignal>
#include <iostream>

#include <util/unicode.h>
#include <util/signal_exception.h>

#include "cbmc_parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
/*
//prospective Windows signal handling code
#include <windows.h>
BOOL WINAPI CCHandler(DWORD);
BOOL WINAPI kill_handler(DWORD dwType) 
{
  switch(dwType) {
    case CTRL_C_EVENT:
    case CTRL_BREAK_EVENT:
      std::cerr << "signal caught" << std::endl;
      exit(1);
      break;
    default:
      break;
  }
  return TRUE;
}
*/
int wmain(int argc, const wchar_t **argv_wide)
{
  /*
  if (!SetConsoleCtrlHandler((PHANDLER_ROUTINE)CCHandler,TRUE)) {
    std::cerr << "Unable to install signal handler!" << std::endl;
    return 243;
  }
  */

  const char **argv=narrow_argv(argc, argv_wide);
  cbmc_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#else
//signal_exceptiont signal_exception;

void kill_handler(int s) 
{
  //std::cerr << "signal caught" << std::endl;
  //exit(1);
  throw signal_exceptiont(s);
}

int main(int argc, const char **argv)
{
  signal(SIGINT,kill_handler);
  cbmc_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#endif
