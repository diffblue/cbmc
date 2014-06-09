/*******************************************************************\

Module: Translation Unit

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "trans_unit.h"

/*******************************************************************\

Function: translation_unit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string translation_unit(const std::string &path)
{
  // convert path into a suggestion for a translation unit name

  std::string unit=path;

  std::string::size_type pos;

  pos=unit.find_last_of("/\\");
  if(pos!=std::string::npos)
    unit=std::string(unit, pos+1);

  pos=unit.find_last_of('.');
  if(pos!=std::string::npos)
    unit=std::string(unit, 0, pos);

  return unit;
}

