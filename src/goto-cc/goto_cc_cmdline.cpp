/*******************************************************************\

Module: Command line interpretation for goto-cc

Author: Daniel Kroening

Date:   April 2010

\*******************************************************************/

/// \file
/// Command line interpretation for goto-cc

#include "goto_cc_cmdline.h"

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <iostream>

#include <util/invariant.h>
#include <util/prefix.h>
#include <util/tempfile.h>

goto_cc_cmdlinet::~goto_cc_cmdlinet()
{
  if(!stdin_file.empty())
  {
    int result=remove(stdin_file.c_str());
    if(result!=0)
    {
      // Let's print the error to stderr instead of ignoring it completely
      std::perror("Remove failed");
    }
  }
}

bool goto_cc_cmdlinet::in_list(const char *option, const char **list)
{
  for(std::size_t i=0; list[i]!=nullptr; i++)
  {
    if(strcmp(option, list[i])==0)
      return true;
  }

  return false;
}

std::size_t goto_cc_cmdlinet::get_optnr(const std::string &opt_string)
{
  optionalt<std::size_t> optnr;
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
    UNREACHABLE;
    return 0;
  }

  // new?
  if(!optnr.has_value())
  {
    options.push_back(option);
    return options.size()-1;
  }

  return *optnr;
}

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

bool goto_cc_cmdlinet::have_infile_arg() const
{
  return std::any_of(
    parsed_argv.cbegin(), parsed_argv.cend(), [](const argt &arg) {
      return arg.is_infile_name;
    });
}
