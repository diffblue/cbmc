/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>

#include <iostream>

#include "cmdline.h"

/*******************************************************************\

Function: cmdlinet::cmdlinet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cmdlinet::cmdlinet()
{
}

/*******************************************************************\

Function: cmdlinet::~cmdlinet 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cmdlinet::~cmdlinet()
{
  clear();
}

/*******************************************************************\

Function: cmdlinet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cmdlinet::clear()
{
  options.clear();
  args.clear();
}

/*******************************************************************\

Function: cmdlinet::isset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cmdlinet::isset(char option) const
{
  int i=getoptnr(option);
  if(i<0) return false;
  return options[i].isset;
}

/*******************************************************************\

Function: cmdlinet::isset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cmdlinet::isset(const char *option) const
{
  int i=getoptnr(option);
  if(i<0) return false;
  return options[i].isset;
}

/*******************************************************************\

Function: cmdlinet::getval

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *cmdlinet::getval(char option) const
{
  int i=getoptnr(option);
  if(i<0) return "";
  if(options[i].values.empty()) return "";
  return options[i].values.front().c_str();
}

/*******************************************************************\

Function: cmdlinet::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cmdlinet::set(const std::string &option)
{
  int i=getoptnr(option);
  if(i<0) return; // ignore
  options[i].isset=true;
}

/*******************************************************************\

Function: cmdlinet::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cmdlinet::set(const std::string &option, const std::string &value)
{
  int i=getoptnr(option);
  if(i<0) return; // ignore
  options[i].isset=true;
  options[i].values.push_back(value);
}

/*******************************************************************\

Function: cmdlinet::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::list<std::string> &cmdlinet::get_values(char option) const
{
  int i=getoptnr(option);
  assert(i>=0);
  return options[i].values;
}

/*******************************************************************\

Function: cmdlinet::getval

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *cmdlinet::getval(const char *option) const
{
  int i=getoptnr(option);
  if(i<0) return "";
  if(options[i].values.empty()) return "";
  return options[i].values.front().c_str();
}

/*******************************************************************\

Function: cmdlinet::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::list<std::string>& cmdlinet::get_values(const std::string &option) const
{
  int i=getoptnr(option);
  assert(i>=0);
  return options[i].values;
}

/*******************************************************************\

Function: cmdlinet::getoptnr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cmdlinet::getoptnr(char option) const
{
  for(unsigned i=0; i<options.size(); i++)
    if(options[i].optchar==option)
      return i;
  
  return -1;
}

/*******************************************************************\

Function: cmdlinet::getoptnr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cmdlinet::getoptnr(const std::string &option) const
{
  for(unsigned i=0; i<options.size(); i++)
    if(options[i].optstring==option)
      return i;
  
  return -1;
}

/*******************************************************************\

Function: cmdlinet::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cmdlinet::parse(int argc, const char **argv, const char *optstring)
{
  clear();

  while(optstring[0]!=0)
  {
    optiont option;

    if(optstring[0]==':')
    {
      std::cerr << "cmdlinet::parse: Invalid option string" << std::endl;
      abort();
    }

    if(optstring[0]=='(')
    {
      option.islong=true;
      option.optchar=0;
      option.isset=false;
      option.optstring="";

      for(optstring++; optstring[0]!=')' && optstring[0]!=0; optstring++)
        option.optstring+=optstring[0];

      if(optstring[0]==')') optstring++;
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
      int optnr;

      if(argv[i][1]=='-')
        optnr=getoptnr(argv[i]+2);
      else
        optnr=getoptnr(argv[i][1]);
   
      if(optnr<0) return true;
      options[optnr].isset=true;
      if(options[optnr].hasval)
      {
        if(argv[i][2]==0 || options[optnr].islong)
        {
          i++;
          if(i==argc) return true;
          if(argv[i][0]=='-') return true;
          options[optnr].values.push_back(argv[i]);
        }
        else
          options[optnr].values.push_back(argv[i]+2);
      }
    }
  }

  return false;
}
