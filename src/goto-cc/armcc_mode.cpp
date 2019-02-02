/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// Command line option container

#include "armcc_mode.h"

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <iostream>

#include <util/message.h>
#include <util/prefix.h>
#include <util/config.h>

#include "compile.h"

/// does it.
int armcc_modet::doit()
{
  if(cmdline.isset('?') || cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  compilet compiler(cmdline, message_handler, cmdline.isset("diag_error="));

  #if 0
  bool act_as_ld=
    has_prefix(base_name, "ld") ||
    has_prefix(base_name, "goto-ld") ||
    has_prefix(base_name, "link") ||
    has_prefix(base_name, "goto-link");
  #endif

  const auto verbosity = eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_ERROR, message_handler);

  debug() << "ARM mode" << eom;

  // model validation
  compiler.validate_goto_model = cmdline.isset("validate-goto-model");

  // get configuration
  config.set(cmdline);

  config.ansi_c.mode=configt::ansi_ct::flavourt::ARM;
  config.ansi_c.arch="arm";

  // determine actions to be taken

  if(cmdline.isset('E'))
    compiler.mode=compilet::PREPROCESS_ONLY;
  else if(cmdline.isset('c') || cmdline.isset('S'))
    compiler.mode=compilet::COMPILE_ONLY;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;

  if(cmdline.isset('U'))
    config.ansi_c.undefines=cmdline.get_values('U');

  if(cmdline.isset('L'))
    compiler.library_paths=cmdline.get_values('L');
    // Don't add the system paths!

  // these take precedence over -I
  if(cmdline.isset('J'))
  {
    const std::list<std::string> &values=
      cmdline.get_values('J');

    for(std::list<std::string>::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      config.ansi_c.preprocessor_options.push_back("-J"+*it);
  }

  if(cmdline.isset("preinclude="))
  {
    const std::list<std::string> &values=
      cmdline.get_values("preinclude=");

    for(std::list<std::string>::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      config.ansi_c.preprocessor_options.push_back("--preinclude="+*it);
  }

  // armcc's default is .o
  if(cmdline.isset("default_extension="))
    compiler.object_file_extension=
      cmdline.get_value("default_extension=");
  else
    compiler.object_file_extension="o";

  // note that ARM's default is "unsigned_chars",
  // in contrast to gcc's default!
  if(cmdline.isset("signed_chars"))
    config.ansi_c.char_is_unsigned=false;
  else
    config.ansi_c.char_is_unsigned=true;

  // ARM's default is 16 bits for wchar_t
  if(cmdline.isset("wchar32"))
    config.ansi_c.wchar_t_width=32;
  else
    config.ansi_c.wchar_t_width=16;

  if(cmdline.isset('o'))
  {
    // given goto-armcc -o file1 -o file2, we output to file2, not file1
    compiler.output_file_object=cmdline.get_values('o').back();
    compiler.output_file_executable=cmdline.get_values('o').back();
  }
  else
  {
    compiler.output_file_object.clear();
    compiler.output_file_executable="a.out";
  }

  if(verbosity > messaget::M_STATISTICS)
  {
    std::list<std::string>::iterator it;

    std::cout << "Defines:\n";
    for(it=config.ansi_c.defines.begin();
        it!=config.ansi_c.defines.end();
        it++)
    {
      std::cout << "  " << (*it) << '\n';
    }

    std::cout << "Undefines:\n";
    for(it=config.ansi_c.undefines.begin();
        it!=config.ansi_c.undefines.end();
        it++)
    {
      std::cout << "  " << (*it) << '\n';
    }

    std::cout << "Preprocessor Options:\n";
    for(it=config.ansi_c.preprocessor_options.begin();
        it!=config.ansi_c.preprocessor_options.end();
        it++)
    {
      std::cout << "  " << (*it) << '\n';
    }

    std::cout << "Include Paths:\n";
    for(it=config.ansi_c.include_paths.begin();
        it!=config.ansi_c.include_paths.end();
        it++)
    {
      std::cout << "  " << (*it) << '\n';
    }

    std::cout << "Library Paths:\n";
    for(it=compiler.library_paths.begin();
        it!=compiler.library_paths.end();
        it++)
    {
      std::cout << "  " << (*it) << '\n';
    }

    std::cout << "Output file (object): "
              << compiler.output_file_object << '\n';
    std::cout << "Output file (executable): "
              << compiler.output_file_executable << '\n';
  }

  // Parse input program, convert to goto program, write output
  return compiler.doit() ? EX_USAGE : EX_OK;
}

/// display command line help
void armcc_modet::help_mode()
{
  std::cout << "goto-armcc understands the options "
            << "of armcc plus the following.\n\n";
}
