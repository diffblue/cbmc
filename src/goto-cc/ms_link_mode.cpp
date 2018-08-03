/*******************************************************************\

Module: Visual Studio Link Mode

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Visual Studio Link Mode

#include "ms_link_mode.h"

#include <iostream>

#include <util/config.h>

ms_link_modet::ms_link_modet(goto_cc_cmdlinet &_cmdline)
  : goto_cc_modet(_cmdline, "link", message_handler)
{
}

/// does it.
int ms_link_modet::doit()
{
  if(cmdline.isset("help"))
  {
    help();
    return 0;
  }

  eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_ERROR, message_handler);

  compilet compiler(cmdline, message_handler, false);

  // determine actions to be undertaken
  compiler.mode = compilet::LINK_LIBRARY;

  // get configuration
  config.set(cmdline);

  compiler.object_file_extension = "obj";

  if(cmdline.isset("LIBPATH"))
    compiler.library_paths = cmdline.get_values("LIBPATH");
  // Don't add the system paths!

  if(cmdline.isset("OUT"))
  {
    compiler.output_file_executable = cmdline.get_values("OUT").back();
  }
  else
  {
    compiler.output_file_object = "";
    compiler.output_file_executable = "a.out";
  }

  // We now iterate over any input files

  for(const auto &arg : cmdline.parsed_argv)
    if(arg.is_infile_name)
      compiler.add_input_file(arg.arg);

  // do all the rest
  if(compiler.doit())
    return 1;

  return 0;
}

/// display command line help
void ms_link_modet::help_mode()
{
  std::cout << "goto-link understands the options of "
            << "link plus the following.\n\n";
}
