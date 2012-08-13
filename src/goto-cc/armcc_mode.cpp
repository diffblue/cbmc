/*******************************************************************\

Module: Command line option container

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <iostream>
#include <cstdlib>

#include <message.h>
#include <prefix.h>
#include <config.h>

#include "armcc_mode.h"
#include "compile.h"
#include "version.h"

/*******************************************************************\

Function: armcc_modet::doit

  Inputs:

 Outputs:

 Purpose: does it.

\*******************************************************************/

bool armcc_modet::doit()
{
  int verbosity=1;

  compilet compiler(cmdline);

  if(has_prefix(base_name, "ld") ||
     has_prefix(base_name, "goto-ld") ||
     has_prefix(base_name, "link") ||
     has_prefix(base_name, "goto-link"))
    compiler.act_as_ld=true;

  if(cmdline.isset("verbosity"))
    verbosity=atoi(cmdline.getval("verbosity"));

  compiler.set_verbosity(verbosity);
  set_verbosity(verbosity);

  debug("ARM mode");
  
  // get configuration
  config.set(cmdline);

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

Function: armcc_modet::help_mode

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void armcc_modet::help_mode()
{
  std::cout << "goto-armcc understands the options of armcc plus the following.\n\n";
}


