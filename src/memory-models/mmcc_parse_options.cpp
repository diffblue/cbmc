/*******************************************************************\

Module: mmcc Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>

#include <util/cout_message.h>

#include <cbmc/version.h>

#include "mm_parser.h"
#include "mmcc_parse_options.h"

/*******************************************************************\

Function: mmcc_parse_optionst::mmcc_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mmcc_parse_optionst::mmcc_parse_optionst(int argc, const char **argv):
  parse_options_baset(MMCC_OPTIONS, argc, argv)
{
}
  
/*******************************************************************\

Function: mmcc_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int mmcc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }
  
  if(cmdline.args.size()==1)
  {
    std::ifstream in(cmdline.args[0].c_str());
    
    if(!in)
    {
      std::cerr << "failed to open `" << cmdline.args[0] << "'\n";
      return 2;
    }

    return convert(in);    
  }
  else if(cmdline.args.size()==0)
  {
    return convert(std::cin);
  }
  else
  {
    usage_error();
    return 1;
  }
  
  return 0;
}

/*******************************************************************\

Function: mmcc_parse_optionst::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int mmcc_parse_optionst::convert(std::istream &in)
{
  console_message_handlert message_handler;
  
  mm_parser.set_message_handler(message_handler);
  mm_parser.in=&in;
  
  if(mm_parser.parse())
  {
    std::cerr << "parse error, giving up\n";
    return 3;
  }
  
  return 0;
}

/*******************************************************************\

Function: mmcc_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void mmcc_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *   MMCC " CBMC_VERSION " - Copyright (C) 2015-2015    * *\n";
    
  std::cout <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " mmcc [-?] [-h] [--help]      show help\n"
    " mmcc file.cat                convert given source file\n"
    " mmcc                         convert from stdin\n"
    "\n";
}
