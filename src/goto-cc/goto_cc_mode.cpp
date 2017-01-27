/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <cstdio>
#include <iostream>

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <cbmc/version.h>

#include "goto_cc_mode.h"

/*******************************************************************\

Function: goto_cc_modet::goto_cc_modet

  Inputs:

 Outputs:

 Purpose: constructor

\*******************************************************************/

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

/*******************************************************************\

Function: goto_cc_modet::~goto_cc_modet

  Inputs:

 Outputs:

 Purpose: constructor

\*******************************************************************/

goto_cc_modet::~goto_cc_modet()
{
}

/*******************************************************************\

Function: goto_cc_modet::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void goto_cc_modet::help()
{
  std::cout <<
  "\n"
  // NOLINTNEXTLINE(whitespace/line_length)
  "* *         goto-cc " CBMC_VERSION "  - Copyright (C) 2006-2014          * *\n"
  "* *        Daniel Kroening, Christoph Wintersteiger         * *\n"
  "* *                 kroening@kroening.com                   * *\n"
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
}

/*******************************************************************\

Function: goto_cc_modet::main

  Inputs: argc/argv

 Outputs: error code

 Purpose: starts the compiler

\*******************************************************************/

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

  catch(const std::string e)
  {
    error() << e << eom;
    return EX_SOFTWARE;
  }

  catch(int)
  {
    return EX_SOFTWARE;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return EX_SOFTWARE;
  }
}

/*******************************************************************\

Function: goto_cc_modet::usage_error

  Inputs: none

 Outputs: none

 Purpose: prints a message informing the user about incorrect options

\*******************************************************************/

void goto_cc_modet::usage_error()
{
  std::cerr << "Usage error!\n\n";
  help();
}
