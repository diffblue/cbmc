/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "str_getline.h"

/*******************************************************************\

Function: str_getline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::istream &str_getline(std::istream &in, std::string &dest)
{
  #define BUFSIZE 4096

  char buffer[BUFSIZE];
  char ch;
  unsigned i=0;

  dest.erase();
  buffer[0]=0;

  while(in)
  {
    if(!in.get(ch))
      break;

    if(ch=='\r') continue;
    if(ch=='\n') break;

    buffer[i++]=ch;
    buffer[i]=0;

    if(i==(BUFSIZE-1))
    {
      dest+=buffer;
      i=0;
      buffer[0]=0;
    }
  }

  dest+=buffer;

  return in;
}
