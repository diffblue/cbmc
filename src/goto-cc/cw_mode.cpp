/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// Command line option container

#include "cw_mode.h"

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
int cw_modet::doit()
{
  if(cmdline.isset('?') || cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  compilet compiler(cmdline, message_handler, cmdline.isset("Werror"));

  #if 0
  bool act_as_ld=
    has_prefix(base_name, "ld") ||
    has_prefix(base_name, "goto-ld") ||
    has_prefix(base_name, "link") ||
    has_prefix(base_name, "goto-link");
  #endif

  const auto verbosity = eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_ERROR, message_handler);

  debug() << "CodeWarrior mode" << eom;

  // model validation
  compiler.validate_goto_model = cmdline.isset("validate-goto-model");

  // get configuration
  config.set(cmdline);

  config.ansi_c.mode=configt::ansi_ct::flavourt::CODEWARRIOR;

  compiler.object_file_extension="o";

  // determine actions to be taken
  if(cmdline.isset('E'))
    compiler.mode=compilet::PREPROCESS_ONLY;
  else if(cmdline.isset('c') || cmdline.isset('S'))
    compiler.mode=compilet::COMPILE_ONLY;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;

  if(cmdline.isset('U'))
    config.ansi_c.undefines=cmdline.get_values('U');

  if(cmdline.isset("undef"))
    config.ansi_c.preprocessor_options.push_back("-undef");

  if(cmdline.isset("nostdinc"))
    config.ansi_c.preprocessor_options.push_back("-nostdinc");

  if(cmdline.isset('L'))
    compiler.library_paths=cmdline.get_values('L');
    // Don't add the system paths!

  if(cmdline.isset('l'))
    compiler.libraries=cmdline.get_values('l');

  if(cmdline.isset('o'))
  {
    // given gcc -o file1 -o file2,
    // gcc will output to file2, not file1
    compiler.output_file_object=cmdline.get_values('o').back();
    compiler.output_file_executable=cmdline.get_values('o').back();
  }
  else
  {
    compiler.output_file_object.clear();
    compiler.output_file_executable="a.out";
  }

  if(cmdline.isset("Wp,"))
  {
    const std::list<std::string> &values=
      cmdline.get_values("Wp,");

    for(std::list<std::string>::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      config.ansi_c.preprocessor_options.push_back("-Wp,"+*it);
  }

  if(cmdline.isset("isystem"))
  {
    const std::list<std::string> &values=
      cmdline.get_values("isystem");

    for(std::list<std::string>::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      config.ansi_c.preprocessor_options.push_back("-isystem "+*it);
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
void cw_modet::help_mode()
{
  std::cout << "goto-cw understands the options of "
            << "gcc (mwcc mode) plus the following.\n\n";
}
