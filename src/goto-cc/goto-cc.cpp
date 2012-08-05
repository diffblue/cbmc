/*******************************************************************\
 
Module: GOTO-CC Main Module
 
Authors: Daniel Kroening, kroening@kroening.com
 
Date: May 2006
 
\*******************************************************************/

#include <algorithm>
#include <iostream>

#include <unicode.h>

#include "cmdline_options.h"
#include "get_base_name.h"
#include "gcc_cmdline.h"
#include "armcc_cmdline.h"
#include "ms_cl_cmdline.h"

/*******************************************************************\
 
Function: to_lower_string
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

std::string to_lower_string(const std::string &s)
{
  std::string result=s;
  transform(result.begin(), result.end(), result.begin(), tolower);
  return result;
}

/*******************************************************************\
 
Function: main
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
#else
int main(int argc, const char **argv)
#endif
{  
  #ifdef _MSC_VER
  const char **argv=narrow_argv(argc, argv_wide);
  #endif

  if(argv==NULL || argc<1)
  {
    std::cerr << "failed to determine base name" << std::endl;
    return 1;
  }
  
  // we do 'to_lower_string' because of Windows
  std::string base_name=
    to_lower_string(get_base_name(argv[0]));
  
  if(base_name=="goto-link" || base_name=="link" ||
     base_name=="goto-cl" || base_name=="cl")
  {
    // this is the Visual Studio personality
    ms_cl_cmdlinet cmdline;
    cmdline.parse_env();
    cmdline_optionst cmdline_options(cmdline);
    cmdline_options.my_name=base_name;
    return cmdline_options.main(argc, argv);
  }
  else if(base_name=="goto-cw" ||
          base_name=="goto-cw-link")
  {
    // this is the CodeWarrior personality,
    // but we use the gcc command line interface
    gcc_cmdlinet cmdline;
    cmdline.mode=goto_cc_cmdlinet::CODEWARRIOR;
    cmdline_optionst cmdline_options(cmdline);
    cmdline_options.my_name=base_name;
    return cmdline_options.main(argc, argv);
  }
  else if(base_name=="goto-armcc" ||
          base_name=="goto-armlink")
  {
    // this is the armcc personality
    armcc_cmdlinet cmdline;
    cmdline_optionst cmdline_options(cmdline);
    cmdline_options.my_name=base_name;
    return cmdline_options.main(argc, argv);
  }
  else
  {
    // the default personality is GCC  
    gcc_cmdlinet cmdline;
    cmdline_optionst cmdline_options(cmdline);
    cmdline_options.my_name=base_name;
    return cmdline_options.main(argc, argv);
  }
}
