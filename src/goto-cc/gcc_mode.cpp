/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <iostream>

#if 0
#include <list>
#include <algorithm>
#include <cctype>

#include <message.h>
#include <stdlib.h>
#include <i2string.h>

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include "cmdline_options.h"
#endif

#include <config.h>
#include <prefix.h>

#include "compile.h"
#include "version.h"

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

  if(has_prefix(base_name, "ld") ||
     has_prefix(base_name, "goto-ld"))
    compiler.act_as_ld=true;

  if(cmdline.isset('v'))
  {
    // This a) prints the version and b) increases verbosity.
    // Compilation continues!
    
    if(compiler.act_as_ld)
      print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
    else
      print("gcc version 3.4.4 (goto-cc " GOTOCC_VERSION ")");
  }

  if(cmdline.isset("version"))
  {
    if(compiler.act_as_ld)
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

  if(cmdline.isset("i386-win32") ||
     cmdline.isset("winx64"))
  {
    // We may wish to reconsider the below.
    config.ansi_c.mode=configt::ansi_ct::MODE_VISUAL_STUDIO;
    debug("Enabling Visual Studio syntax");
  }
  else if(cmdline.mode==goto_cc_cmdlinet::GCC)
    config.ansi_c.mode=configt::ansi_ct::MODE_GCC;
  else if(cmdline.mode==goto_cc_cmdlinet::CODEWARRIOR)
    config.ansi_c.mode=configt::ansi_ct::MODE_CODEWARRIOR;

  compiler.object_file_extension="o";

  if(cmdline.isset('E'))
    compiler.only_preprocess=true;

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

  compiler.doLink=!(cmdline.isset('c') || cmdline.isset('S'));

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

  // Parse input program, convert to goto program, write output
  return compiler.doit();
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

