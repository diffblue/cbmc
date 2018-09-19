/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// Command line option container

#include "goto_cc_mode.h"

#include <cstdio>
#include <iostream>

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <util/exception_utils.h>
#include <util/parse_options.h>
#include <util/version.h>

/// constructor
goto_cc_modet::goto_cc_modet(
  goto_cc_cmdlinet &_cmdline,
  const std::string &_base_name,
  message_handlert &_message_handler):
  messaget(_message_handler),
  cmdline(_cmdline),
  base_name(_base_name)
{
  register_languages();
}

/// constructor
goto_cc_modet::~goto_cc_modet()
{
}

/// display command line help
void goto_cc_modet::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("goto-cc", CBMC_VERSION) << '\n'
            <<
  "* *               Copyright (C) 2006-2018                   * *\n"
  "* *          Daniel Kroening, Michael Tautschnig,           * *\n"
  "* *               Christoph Wintersteiger                   * *\n"
  "\n";

  help_mode();

  std::cout <<
  "Usage:                       Purpose:\n"
  "\n"
  " --verbosity #               verbosity level\n"
  " --function name             set entry point to name\n"
  " --native-compiler cmd       command to invoke as preprocessor/compiler\n"
  " --native-linker cmd         command to invoke as linker\n"
  " --native-assembler cmd      command to invoke as assembler (goto-as only)\n"
  " --print-rejected-preprocessed-source file\n"
  "                             copy failing (preprocessed) source to file\n"
  "\n";
  // clang-format on
}

/// starts the compiler
/// \return error code
int goto_cc_modet::main(int argc, const char **argv)
{
  if(cmdline.parse(argc, argv))
  {
    usage_error();
    return EX_USAGE;
  }

  try
  {
    return doit();
  }

  catch(const char *e)
  {
    error() << e << eom;
    return EX_SOFTWARE;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return EX_SOFTWARE;
  }

  catch(int)
  {
    return EX_SOFTWARE;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return EX_SOFTWARE;
  }
  catch(const cprover_exception_baset &e)
  {
    error() << e.what() << eom;
    return EX_SOFTWARE;
  }
}

/// prints a message informing the user about incorrect options
/// \return none
void goto_cc_modet::usage_error()
{
  std::cerr << "Usage error!\n\n";
  help();
}
