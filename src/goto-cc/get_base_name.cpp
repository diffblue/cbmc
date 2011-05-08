/*******************************************************************\

Module: 

Author: CM Wintersteiger

Date: 

\*******************************************************************/

#include "get_base_name.h"

/*******************************************************************\

Function: get_base_name

  Inputs: a string

 Outputs: a new string

 Purpose: cleans a filename from paths and extensions

\*******************************************************************/

std::string get_base_name(const std::string &in)
{
  size_t r=in.rfind('.', in.length()-1);
  if(r==std::string::npos) r=in.length();

  size_t f=in.rfind('/', in.length()-1);
  if(f==std::string::npos) f=0;

  size_t fw=in.rfind('\\', in.length()-1);
  if(fw==std::string::npos) fw=0;

  f = (fw>f)?fw:f;

  if(in[f]=='/' || in[f]=='\\') f++;
  return in.substr(f, r-f);
}
