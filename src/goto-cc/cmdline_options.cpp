/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <iostream>
#include <list>
#include <algorithm>
#include <cctype>
#include <cstdlib>

#include <message.h>
#include <prefix.h>
#include <config.h>

#include "cmdline_options.h"
#include "compile.h"
#include "version.h"

/*******************************************************************\

Function: cmdline_optionst::cmdline_optionst

  Inputs: 

 Outputs: 

 Purpose: constructor

\*******************************************************************/

cmdline_optionst::cmdline_optionst(goto_cc_cmdlinet &_cmdline):
  goto_cc_modet(_cmdline),
  cmdline(_cmdline)
{
}

/*******************************************************************\

Function: cmdline_optionst::doit

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

bool cmdline_optionst::doit()
{
  int verbosity=1;

  compilet compiler(cmdline);

  if(has_prefix(base_name, "ld") ||
     has_prefix(base_name, "goto-ld") ||
     has_prefix(base_name, "link") ||
     has_prefix(base_name, "goto-link"))
    compiler.act_as_ld=true;

  if(cmdline.mode==goto_cc_cmdlinet::GCC)
  {
    if(cmdline.isset('v'))
    {
      // This a) prints the version and b) increases verbosity.
      // Compilation continues.
      
      if(compiler.act_as_ld)
        print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
      else
        print("gcc version 3.4.4 (goto-cc " GOTOCC_VERSION ")");
    }

    if(cmdline.isset("version"))
    {
      if(compiler.act_as_ld)
      {
        print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
      }
      else
      {
        print("gcc (GCC) 3.4.4 (goto-cc " GOTOCC_VERSION ")\n");
      }

      print("Copyright (C) 2006-2012 Daniel Kroening, Christoph Wintersteiger\n");

      return false;
    }

    if(cmdline.isset("dumpversion"))
    {
      std::cout << "3.4.4" << std::endl;
      return false;
    }

    if(cmdline.isset("Wall"))
      verbosity=2;
  }

  if(cmdline.isset("verbosity"))
    verbosity=atoi(cmdline.getval("verbosity"));

  compiler.set_verbosity(verbosity);
  set_verbosity(verbosity);

  switch(cmdline.mode)
  {
  case goto_cc_cmdlinet::GCC:
    debug("GCC mode");
    break;

  case goto_cc_cmdlinet::VISUAL_STUDIO:
    debug("Visual Studio mode");
    break;

  case goto_cc_cmdlinet::CODEWARRIOR:
    debug("CodeWarrior mode");
    break;
    
  case goto_cc_cmdlinet::ARM:
    debug("ARM mode");
    break;
    
  default:;
    assert(false);
  }
  
  // get configuration
  config.set(cmdline);

  if(cmdline.mode==goto_cc_cmdlinet::GCC ||
     cmdline.mode==goto_cc_cmdlinet::CODEWARRIOR)
  {
    if(cmdline.isset("i386-win32") ||
       cmdline.isset("winx64"))
    {
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
  }
  else if(cmdline.mode==goto_cc_cmdlinet::ARM)
  {
    config.ansi_c.mode=configt::ansi_ct::MODE_ARM;

    if(cmdline.isset('E'))
      compiler.only_preprocess=true;

    if(cmdline.isset('U'))
      config.ansi_c.undefines=cmdline.get_values('U');

    if(cmdline.isset('L'))
      compiler.library_paths=cmdline.get_values('L');
      // Don't add the system paths!

    compiler.doLink=!(cmdline.isset('c') || cmdline.isset('S'));

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
        cmdline.getval("default_extension=");
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
      compiler.output_file_object="";
      compiler.output_file_executable="a.out";
    }
  }
  else if(cmdline.mode==goto_cc_cmdlinet::VISUAL_STUDIO)
  {
    config.ansi_c.mode=configt::ansi_ct::MODE_VISUAL_STUDIO;
    compiler.object_file_extension="obj";

    if(cmdline.isset('E') || cmdline.isset('P'))
      compiler.only_preprocess=true;

    compiler.doLink=!( cmdline.isset('E') || cmdline.isset('P') ||
                       cmdline.isset('c') );
                       
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

Function: cmdline_optionst::help_mode

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void cmdline_optionst::help_mode()
{
  switch(cmdline.mode)
  {
  case goto_cc_cmdlinet::VISUAL_STUDIO:
    std::cout << "goto-cl understands the options of CL plus the following.\n\n";
    break;
    
  case goto_cc_cmdlinet::GCC:
    std::cout << "goto-cc understands the options of gcc plus the following.\n\n";
    break;
    
  case goto_cc_cmdlinet::CODEWARRIOR:
    std::cout << "goto-cw understands the options of gcc (mwcc mode) plus the following.\n\n";
    break;
    
  case goto_cc_cmdlinet::ARM:
    std::cout << "goto-armcc understands the options of armcc plus the following.\n\n";
    break;
    
  default:
    assert(false);
  }
}

