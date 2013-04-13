/*******************************************************************\

Module: Visual Studio CL Mode

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <iostream>
#include <cstdlib>

#include <util/message.h>
#include <util/prefix.h>
#include <util/config.h>

#include "ms_cl_mode.h"
#include "compile.h"
#include "version.h"

/*******************************************************************\

Function: ms_cl_modet::doit

  Inputs:

 Outputs:

 Purpose: does it.

\*******************************************************************/

static bool is_directory(const std::string &s)
{
  if(s.size()<1) return false;
  char last_char=s[s.size()-1];
  // Visual CL recognizes both
  return last_char=='\\' || last_char=='/';
}

bool ms_cl_modet::doit()
{
  if(cmdline.isset('?') || 
     cmdline.isset("help"))
  {
    help();
    return false;
  }

  int verbosity=1;

  compilet compiler(cmdline);

  #if 0  
  bool act_as_ld=
    has_prefix(base_name, "link") ||
    has_prefix(base_name, "goto-link");
  #endif

  if(cmdline.isset("verbosity"))
    verbosity=atoi(cmdline.getval("verbosity"));

  compiler.set_verbosity(verbosity);
  set_verbosity(verbosity);

  debug("Visual Studio mode");
  
  // get configuration
  config.set(cmdline);

  config.ansi_c.mode=configt::ansi_ct::MODE_VISUAL_STUDIO;
  compiler.object_file_extension="obj";
  
  // determine actions to be undertaken

  if(cmdline.isset('E') || cmdline.isset('P'))
    compiler.mode=compilet::PREPROCESS_ONLY;
  else if(cmdline.isset('c'))
    compiler.mode=compilet::COMPILE_ONLY;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;
                     
  compiler.echo_file_name=true;

  if(cmdline.isset("Fo"))
  {
    compiler.output_file_object=cmdline.getval("Fo");

    // this could be a directory
    if(is_directory(compiler.output_file_object))
    {
      if(cmdline.args.size()>=1)
        compiler.output_file_object+=get_base_name(cmdline.args[0])+".obj";
    }
  }

  if(cmdline.isset("Fe"))
  {
    compiler.output_file_executable=cmdline.getval("Fe");

    // this could be a directory
    if(is_directory(compiler.output_file_executable))
    {
      if(cmdline.args.size()>=1)
        compiler.output_file_executable+=get_base_name(cmdline.args[0])+".exe";
    }
  }
  else
  {
    // We need at least one argument.
    // CL uses the first file name it gets!
    if(cmdline.args.size()>=1)
      compiler.output_file_executable=get_base_name(cmdline.args[0])+".exe";
  }

  if(verbosity>8)
  {
    std::list<std::string>::iterator it;

    std::cout << "Defines:\n";
    for(it=config.ansi_c.defines.begin();
        it!=config.ansi_c.defines.end();
        it++)
    {
      std::cout << "  " << (*it) << std::endl;
    }

    std::cout << "Undefines:\n";
    for(it=config.ansi_c.undefines.begin();
        it!=config.ansi_c.undefines.end();
        it++)
    {
      std::cout << "  " << (*it) << std::endl;
    }

    std::cout << "Preprocessor Options:\n";
    for(it=config.ansi_c.preprocessor_options.begin();
        it!=config.ansi_c.preprocessor_options.end();
        it++)
    {
      std::cout << "  " << (*it) << std::endl;
    }

    std::cout << "Include Paths:\n";
    for(it=config.ansi_c.include_paths.begin();
        it!=config.ansi_c.include_paths.end();
        it++)
    {
      std::cout << "  " << (*it) << std::endl;
    }

    std::cout << "Library Paths:\n";
    for(it=compiler.library_paths.begin();
        it!=compiler.library_paths.end();
        it++)
    {
      std::cout << "  " << (*it) << std::endl;
    }

    std::cout << "Output file (object): " << compiler.output_file_object << std::endl;
    std::cout << "Output file (executable): " << compiler.output_file_executable << std::endl;
  }

  // Parse input program, convert to goto program, write output
  return compiler.doit();
}

/*******************************************************************\

Function: ms_cl_modet::help_mode

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void ms_cl_modet::help_mode()
{
  std::cout << "goto-cl understands the options of CL plus the following.\n\n";
}


