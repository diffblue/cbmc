/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <cstdlib>
#include <iostream>

#if 0
#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif
#endif

#include <tempdir.h>
#include <config.h>
#include <prefix.h>
#include <suffix.h>

#include "compile.h"
#include "version.h"
#include "run.h"

#include "gcc_mode.h"

/*******************************************************************\

Function: gcc_modet::doit

  Inputs:

 Outputs:

 Purpose: does it.

\*******************************************************************/

bool gcc_modet::doit()
{
  int verbosity=1;

  compilet compiler(cmdline);
  
  bool act_as_ld=
    has_prefix(base_name, "ld") ||
    has_prefix(base_name, "goto-ld");

  if(cmdline.isset('v'))
  {
    // This a) prints the version and b) increases verbosity.
    // Compilation continues, don't exit!
    
    if(act_as_ld)
      print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
    else
      print("gcc version 3.4.4 (goto-cc " GOTOCC_VERSION ")");
  }

  if(cmdline.isset("version"))
  {
    if(act_as_ld)
      print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
    else
      print("gcc (GCC) 3.4.4 (goto-cc " GOTOCC_VERSION ")\n");

    print("Copyright (C) 2006-2012 Daniel Kroening, Christoph Wintersteiger\n");

    return false; // Exit!
  }

  if(cmdline.isset("dumpversion"))
  {
    std::cout << "3.4.4" << std::endl;
    return false;
  }

  if(cmdline.isset("Wall"))
    verbosity=2;

  if(cmdline.isset("verbosity"))
    verbosity=atoi(cmdline.getval("verbosity"));

  compiler.set_verbosity(verbosity);
  set_verbosity(verbosity);

  debug("GCC mode");
  
  // get configuration
  config.set(cmdline);
  
  if(cmdline.isset("m32"))
    config.ansi_c.set_32();
  else if(cmdline.isset("m64"))
    config.ansi_c.set_64();

  // determine actions to be undertaken
  
  if(act_as_ld)
    compiler.mode=compilet::LINK_LIBRARY;
  else if(cmdline.isset('c') || cmdline.isset('S'))
    compiler.mode=compilet::COMPILE_ONLY;
  else if(cmdline.isset('E'))
    compiler.mode=compilet::PREPROCESS_ONLY;
  else if(cmdline.isset("shared") ||
          cmdline.isset('r')) // really not well documented
    compiler.mode=compilet::COMPILE_LINK;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;
    
  switch(compiler.mode)
  {
  case compilet::LINK_LIBRARY: debug("Linking a library only"); break;
  case compilet::COMPILE_ONLY: debug("Compiling only"); break;
  case compilet::PREPROCESS_ONLY: debug("Preprocessing only"); break;
  case compilet::COMPILE_LINK: debug("Compiling and linking a library"); break;
  case compilet::COMPILE_LINK_EXECUTABLE: debug("Compiling and linking an executable"); break;
  default: assert(false);
  }

  if(cmdline.isset("i386-win32") ||
     cmdline.isset("winx64"))
  {
    // We may wish to reconsider the below.
    config.ansi_c.mode=configt::ansi_ct::MODE_VISUAL_STUDIO;
    debug("Enabling Visual Studio syntax");
  }
  else
    config.ansi_c.mode=configt::ansi_ct::MODE_GCC;

  compiler.object_file_extension="o";
  
  if(cmdline.isset("std"))
  {
    std::string std_string=cmdline.getval("std");
    if(std_string=="gnu99" || std_string=="c99" ||
       std_string=="gnu9x" || std_string=="c9x" ||
       std_string=="gnu11" || std_string=="c11" ||
       std_string=="gnu1x" || std_string=="c1x")
      config.ansi_c.for_has_scope=true;
  }

  // gcc's default is 32 bits for wchar_t
  if(cmdline.isset("short-wchar"))
    config.ansi_c.wchar_t_width=16;

  // gcc's default is 64 bits for double
  if(cmdline.isset("short-double"))
    config.ansi_c.double_width=32;
    
  // gcc's default is signed chars
  if(cmdline.isset("funsigned-char"))
    config.ansi_c.char_is_unsigned=true;

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
    compiler.output_file_object="";
    compiler.output_file_executable="a.out";
  }
    
  // Iterate over file arguments, and do any preprocessing needed

  temp_dirt temp_dir("goto-cc-XXXXXX");

  for(cmdlinet::argst::iterator
      a_it=cmdline.args.begin();
      a_it!=cmdline.args.end();
      a_it++)
  {
    if(has_suffix(*a_it, ".c") ||
       has_suffix(*a_it, ".cc") ||
       has_suffix(*a_it, ".cp") ||
       has_suffix(*a_it, ".cpp") ||
       has_suffix(*a_it, ".CPP") ||
       has_suffix(*a_it, ".c++") ||
       has_suffix(*a_it, ".C"))
    {
      std::string new_suffix=has_suffix(*a_it, ".c")?".i":".ii";
      std::string new_name=get_base_name(*a_it)+new_suffix;
      std::string dest=temp_dir(new_name);
      int exit_code=preprocess(*a_it, dest);
      if(exit_code!=0)
      {
        debug("preprocessing has failed");
        return true;
      }
      
      *a_it=dest;
    }
  }

  // do all the rest
  bool result=compiler.doit();
  
  return result;
}

/*******************************************************************\

Function: gcc_modet::preprocess

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

int gcc_modet::preprocess(const std::string &src, const std::string &dest)
{
  // build new argv
  std::vector<std::string> new_argv;
  
  new_argv.reserve(cmdline.parsed_argv.size());

  bool skip_next=false;
  
  for(gcc_cmdlinet::parsed_argvt::const_iterator
      it=cmdline.parsed_argv.begin();
      it!=cmdline.parsed_argv.end();
      it++)
  {
    if(skip_next)
    {
      // skip
      skip_next=false;
    }
    else if(it->is_infile_name)
    {
      // skip
    }
    else if(it->arg=="-c" || it->arg=="-E" || it->arg=="-S")
    {
      // skip
    }
    else if(it->arg=="-o")
    {
      skip_next=true;
    }
    else if(has_prefix(it->arg, "-o"))
    {
      // ignore
    }
    else if(it->arg=="--function" || it->arg=="--verbosity")
    {
      // ignore here
      skip_next=true;
    }
    else
      new_argv.push_back(it->arg);
  }

  // We just want to preprocess.
  new_argv.push_back("-E");

  // destination file
  new_argv.push_back("-o");
  new_argv.push_back(dest);
  
  // source file  
  new_argv.push_back(src);
  
  // overwrite argv[0]
  assert(new_argv.size()>=1);
  new_argv[0]="gcc";
  
  #if 0
  std::cout << "RUN:";
  for(unsigned i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif
  
  return run("gcc", new_argv);
}

/*******************************************************************\

Function: gcc_modet::help_mode

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void gcc_modet::help_mode()
{
  std::cout << "goto-cc understands the options of gcc plus the following.\n\n";
}

