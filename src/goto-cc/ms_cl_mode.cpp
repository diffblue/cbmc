/*******************************************************************\

Module: Visual Studio CL Mode

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// Visual Studio CL Mode

#include "ms_cl_mode.h"

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
#include <util/get_base_name.h>

#include "compile.h"

/// does it.
static bool is_directory(const std::string &s)
{
  if(s.empty())
    return false;
  char last_char=s[s.size()-1];
  // Visual CL recognizes both
  return last_char=='\\' || last_char=='/';
}

int ms_cl_modet::doit()
{
  if(cmdline.isset('?') ||
     cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  compilet compiler(cmdline, message_handler, cmdline.isset("WX"));

  #if 0
  bool act_as_ld=
    has_prefix(base_name, "link") ||
    has_prefix(base_name, "goto-link");
  #endif

  const auto verbosity = eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_ERROR, message_handler);

  debug() << "Visual Studio mode" << eom;

  // get configuration
  config.set(cmdline);

  config.ansi_c.mode=configt::ansi_ct::flavourt::VISUAL_STUDIO;
  compiler.object_file_extension="obj";

  // determine actions to be undertaken

  if(cmdline.isset('E') || cmdline.isset('P'))
    compiler.mode=compilet::PREPROCESS_ONLY;
  else if(cmdline.isset('c'))
    compiler.mode=compilet::COMPILE_ONLY;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;

  if(cmdline.isset("std"))
  {
    const std::string std_string = cmdline.get_value("std");

    if(
      std_string == ":c++14" || std_string == "=c++14" ||
      std_string == ":c++17" || std_string == "=c++17" ||
      std_string == ":c++latest" || std_string == "=c++latest")
    {
      // we don't have any newer version at the moment
      config.cpp.set_cpp14();
    }
    else if(std_string == ":c++11" || std_string == "=c++11")
    {
      // this isn't really a Visual Studio variant, we just do this for GCC
      // command-line compatibility
      config.cpp.set_cpp11();
    }
    else
      warning() << "unknown language standard " << std_string << eom;
  }
  else
    config.cpp.set_cpp14();

  compiler.echo_file_name=true;

  if(cmdline.isset("Fo"))
  {
    std::string Fo_value = cmdline.get_value("Fo");

    // this could be a directory or a file name
    if(is_directory(Fo_value))
      compiler.output_directory_object = Fo_value;
    else
      compiler.output_file_object = Fo_value;
  }

  if(cmdline.isset("Fe"))
  {
    compiler.output_file_executable=cmdline.get_value("Fe");

    // this could be a directory
    if(is_directory(compiler.output_file_executable) &&
       cmdline.args.size()>=1)
      compiler.output_file_executable+=
        get_base_name(cmdline.args[0], true)+".exe";
  }
  else
  {
    // We need at least one argument.
    // CL uses the first file name it gets!
    if(cmdline.args.size()>=1)
      compiler.output_file_executable=
        get_base_name(cmdline.args[0], true)+".exe";
  }

  if(cmdline.isset('J'))
    config.ansi_c.char_is_unsigned=true;

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
void ms_cl_modet::help_mode()
{
  std::cout << "goto-cl understands the options of CL plus the following.\n\n";
}
