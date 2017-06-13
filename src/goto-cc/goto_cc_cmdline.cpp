/*******************************************************************\

Module: Command line interpretation for goto-cc

Author: Daniel Kroening

Date:   April 2010

\*******************************************************************/

#include <cstring>
#include <cassert>
#include <iostream>
#include <cstdio>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "goto_cc_cmdline.h"

/*******************************************************************\

Function: goto_cc_cmdlinet::~goto_cc_cmdlinet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_cc_cmdlinet::~goto_cc_cmdlinet()
{
  if(!stdin_file.empty())
    remove(stdin_file.c_str());
}

/*******************************************************************\

Function: goto_cc_cmdlinet::in_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_cc_cmdlinet::in_list(const char *option, const char **list)
{
  for(std::size_t i=0; list[i]!=NULL; i++)
  {
    if(strcmp(option, list[i])==0)
      return true;
  }

  return false;
}

/*******************************************************************\

Function: goto_cc_cmdlinet::prefix_in_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_cc_cmdlinet::prefix_in_list(
  const char *option,
  const char **list,
  std::string &prefix)
{
  for(std::size_t i=0; list[i]!=NULL; i++)
  {
    if(strncmp(option, list[i], strlen(list[i]))==0)
    {
      prefix=std::string(list[i]);
      return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: goto_cc_cmdlinet::get_optnr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t goto_cc_cmdlinet::get_optnr(const std::string &opt_string)
{
  int optnr;
  cmdlinet::optiont option;

  if(has_prefix(opt_string, "--")) // starts with -- ?
  {
    if(opt_string.size()==3) // still "short"
    {
      option.islong=false;
      option.optchar=opt_string[2];
      optnr=getoptnr(option.optchar);
    }
    else
    {
      option.islong=true;
      option.optstring=std::string(opt_string, 2, std::string::npos);
      option.optchar=0;
      optnr=getoptnr(option.optstring);
    }
  }
  else if(has_prefix(opt_string, "-")) // starts with - ?
  {
    if(opt_string.size()==2)
    {
      option.islong=false;
      option.optchar=opt_string[1];
      optnr=getoptnr(option.optchar);
    }
    else
    {
      option.islong=true;
      option.optstring=std::string(opt_string, 1, std::string::npos);
      option.optchar=0;
      optnr=getoptnr(option.optstring);
    }
  }
  else
  {
    assert(false);
    return -1;
  }

  // new?
  if(optnr==-1)
  {
    options.push_back(option);
    return options.size()-1;
  }

  return optnr;
}

/*******************************************************************\

Function: goto_cc_cmdlinet::add_infile_arg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_cc_cmdlinet::add_infile_arg(const std::string &arg)
{
  parsed_argv.push_back(argt(arg));
  parsed_argv.back().is_infile_name=true;

  if(arg=="-")
  {
    stdin_file=get_temporary_file("goto-cc", "stdin");

    FILE *tmp=fopen(stdin_file.c_str(), "wt");

    char ch;
    while(std::cin.read(&ch, 1))
      fputc(ch, tmp);

    fclose(tmp);
  }
}
