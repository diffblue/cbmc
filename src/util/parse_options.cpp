/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#if defined (_WIN32)
#define EX_OK 0
#define EX_USAGE 1
#else
#include <sysexits.h>
#endif

#include "cmdline.h"
#include "parse_options.h"
#include "signal_catcher.h"

/*******************************************************************\

Function: parse_options_baset::parse_options_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

parse_options_baset::parse_options_baset(
  const std::string &_optstring, int argc, const char **argv)
{
  std::string optstring=std::string("?h(help)")+_optstring;
  parse_result=cmdline.parse(argc, argv, optstring.c_str());
}

/*******************************************************************\

Function: parse_options_baset::help

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_options_baset::help()
{
}

/*******************************************************************\

Function: parse_options_baset::usage_error

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_options_baset::usage_error()
{
  std::cerr << "Usage error!\n\n";
  help();
}

/*******************************************************************\

Function: parse_options_baset::main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int parse_options_baset::main()
{
  if(parse_result)
  {
    usage_error();
    return EX_USAGE;
  }

  if(cmdline.isset('?') || cmdline.isset('h') || cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }
  
  // install signal catcher
  install_signal_catcher();

  return doit();
}
