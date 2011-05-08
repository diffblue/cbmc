#include "strstream2string.h"

/*******************************************************************\

Function: strstream2string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strstream2string(std::ostringstream &stream, std::string &dest)
{
  //stream << char(0);
  dest=stream.str();
  //stream.freeze(0);
}

