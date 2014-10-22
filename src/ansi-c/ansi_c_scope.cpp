/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "ansi_c_scope.h"

/*******************************************************************\

Function: ansi_c_scopet::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_scopet::print(std::ostream &out) const
{
  out << "Prefix: " << prefix << "\n";

  for(ansi_c_scopet::name_mapt::const_iterator
      n_it=name_map.begin();
      n_it!=name_map.end();
      n_it++)
  {
    out << "  ID: " << n_it->first
        << " CLASS: " << n_it->second.id_class
        << "\n";
  }
}

