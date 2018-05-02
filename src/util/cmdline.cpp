/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cmdline.h"

#include <util/invariant.h>

cmdlinet::cmdlinet()
{
}

cmdlinet::~cmdlinet()
{
}

void cmdlinet::clear()
{
  options.clear();
  args.clear();
}

bool cmdlinet::isset(char option) const
{
  auto i=getoptnr(option);
  if(i.has_value())
    return options[*i].isset;
  else
    return false;
}

bool cmdlinet::isset(const char *option) const
{
  auto i=getoptnr(option);
  if(i.has_value())
    return options[*i].isset;
  else
    return false;
}

std::string cmdlinet::get_value(char option) const
{
  auto i=getoptnr(option);

  if(i.has_value())
  {
    if(options[*i].values.empty())
      return "";
    else
      return options[*i].values.front();
  }
  else
    return "";
}

void cmdlinet::set(const std::string &option)
{
  auto i=getoptnr(option);

  if(i.has_value())
    options[*i].isset=true;

  // otherwise ignore
}

void cmdlinet::set(const std::string &option, const std::string &value)
{
  auto i=getoptnr(option);

  if(i.has_value())
  {
    options[*i].isset=true;
    options[*i].values.push_back(value);
  }

  // otherwise ignore
}

static std::list<std::string> immutable_empty_list;

const std::list<std::string> &cmdlinet::get_values(char option) const
{
  auto i=getoptnr(option);

  if(i.has_value())
    return options[*i].values;
  else
    return immutable_empty_list;
}

std::string cmdlinet::get_value(const char *option) const
{
  auto i=getoptnr(option);

  if(i.has_value())
  {
    if(options[*i].values.empty())
      return "";
    else
      return options[*i].values.front();
  }
  else
    return "";
}

const std::list<std::string> &cmdlinet::get_values(
  const std::string &option) const
{
  auto i=getoptnr(option);

  if(i.has_value())
    return options[*i].values;
  else
    return immutable_empty_list;
}

optionalt<std::size_t> cmdlinet::getoptnr(char option) const
{
  for(std::size_t i=0; i<options.size(); i++)
    if(options[i].optchar==option)
      return i;

  return optionalt<std::size_t>();
}

optionalt<std::size_t> cmdlinet::getoptnr(const std::string &option) const
{
  for(std::size_t i=0; i<options.size(); i++)
    if(options[i].optstring==option)
      return i;

  return optionalt<std::size_t>();
}

bool cmdlinet::parse(int argc, const char **argv, const char *optstring)
{
  clear();

  while(optstring[0]!=0)
  {
    optiont option;

    DATA_INVARIANT(
      optstring[0] != ':', "cmdlinet::parse: Invalid option string\n");

    if(optstring[0]=='(')
    {
      option.islong=true;
      option.optchar=0;
      option.isset=false;
      option.optstring="";

      for(optstring++; optstring[0]!=')' && optstring[0]!=0; optstring++)
        option.optstring+=optstring[0];

      if(optstring[0]==')')
        optstring++;
    }
    else
    {
      option.islong=false;
      option.optchar=optstring[0];
      option.optstring="";
      option.isset=false;

      optstring++;
    }

    if(optstring[0]==':')
    {
      option.hasval=true;
      optstring++;
    }
    else
      option.hasval=false;

    options.push_back(option);
  }

  for(int i=1; i<argc; i++)
  {
    if(argv[i][0]!='-')
      args.push_back(argv[i]);
    else
    {
      optionalt<std::size_t> optnr;

      if(argv[i][1]!=0 && argv[i][2]==0)
        optnr=getoptnr(argv[i][1]); // single-letter option -X
      else if(argv[i][1]=='-')
        optnr=getoptnr(argv[i]+2); // multi-letter option with --XXX
      else
      {
        // Multi-letter option -XXX, or single-letter with argument -Xval
        // We first try single-letter.
        optnr=getoptnr(argv[i][1]);

        if(!optnr.has_value()) // try multi-letter
          optnr=getoptnr(argv[i]+1);
      }

      if(!optnr.has_value())
      {
        unknown_arg=argv[i];
        return true;
      }

      options[*optnr].isset=true;

      if(options[*optnr].hasval)
      {
        if(argv[i][2]==0 || options[*optnr].islong)
        {
          i++;
          if(i==argc)
            return true;
          if(argv[i][0]=='-' && argv[i][1]!=0)
            return true;
          options[*optnr].values.push_back(argv[i]);
        }
        else
          options[*optnr].values.push_back(argv[i]+2);
      }
    }
  }

  return false;
}
