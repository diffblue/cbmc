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
#include "exception_utils.h"
#include "exit_codes.h"
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
  error_message("Usage error!\n");
  help();
}

/// This can be overloaded so that error messages are valid XML / JSON.
void parse_options_baset::error_message(const std::string &err)
{
  std::cerr << err << '\n';
  return;
}

/// Print an error message mentioning the option that was not recognized when
/// parsing the command line.
void parse_options_baset::unknown_option_msg()
{
  if(!cmdline.unknown_arg.empty())
    error_message("Unknown option: " + cmdline.unknown_arg + "\n");
}

int parse_options_baset::main()
{
  // catch all exceptions here so that this code is not duplicated
  // for each tool
  try
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

  // CPROVER style exceptions in order of decreasing happiness
  catch(const invalid_command_line_argument_exceptiont &e)
  {
    error_message(e.what());
    return CPROVER_EXIT_USAGE_ERROR;
  }
  catch(const cprover_exception_baset &e)
  {
    error_message(e.what());
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(const std::string &e)
  {
    error_message("C++ string exception : " + e);
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(const char *e)
  {
    error_message(std::string("C string exception : ") + e);
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(int e)
  {
    error_message("Numeric exception : " + std::to_string(e));
    return CPROVER_EXIT_EXCEPTION;
  }
  // C++ style exceptions
  catch(const std::bad_alloc &)
  {
    error_message("Out of memory");
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }
  catch(const std::exception &e)
  {
    error_message(e.what());
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(...)
  {
    error_message("Unknown exception type!");
    return CPROVER_EXIT_EXCEPTION;
  }
}

std::string
banner_string(const std::string &front_end, const std::string &version)
{
  const std::string version_str = front_end + " " + version + " " +
                                  std::to_string(sizeof(void *) * 8) + "-bit";

  std::string::size_type left_padding = 0, right_padding = 0;
  if(version_str.size() < 57)
  {
    left_padding = (57 - version_str.size() + 1) / 2;
    right_padding = (57 - version_str.size()) / 2;
  }

  return "* *" + std::string(left_padding, ' ') + version_str +
         std::string(right_padding, ' ') + "* *";
}
