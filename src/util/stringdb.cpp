/*******************************************************************\

Module: String Storage

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include "stringdb.h"

stringdbt stringdb;

/*******************************************************************\

Function: stringdbt::stringdbt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

stringdbt::stringdbt()
{
}

/*******************************************************************\

Function: stringdbt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void stringdbt::output(std::ostream &out) const
{
  for(dstring_storaget::const_iterator
      it=storage.begin();
      it!=storage.end();
      it++)
    out << *it << std::endl;
}

/*******************************************************************\

Function: hash_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

size_t hash_string(const dstring &s)
{
  return hash_string(s.as_string());
}
