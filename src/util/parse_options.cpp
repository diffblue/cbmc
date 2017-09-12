/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "parse_options.h"

#include <iostream>

#if defined (_WIN32)
#define EX_OK 0
#define EX_USAGE 1
#else
#include <sysexits.h>
#endif

#include "cmdline.h"
#include "signal_catcher.h"

parse_options_baset::parse_options_baset(
  const std::string &_optstring, int argc, const char **argv)
{
  std::string optstring=std::string("?h(help)")+_optstring;
  parse_result=cmdline.parse(argc, argv, optstring.c_str());
}

void parse_options_baset::help()
{
}

void parse_options_baset::usage_error()
{
  std::cerr << "Usage error!\n\n";
  help();
}

/// Print an error message mentioning the option that was not recognized when
/// parsing the command line.
void parse_options_baset::unknown_option_msg()
{
  if(!cmdline.unknown_arg.empty())
    std::cerr << "Unknown option: " << cmdline.unknown_arg << "\n";
}

int parse_options_baset::main()
{
  if(parse_result)
  {
    usage_error();
    unknown_option_msg();
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
