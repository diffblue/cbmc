/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "ansi_c_parse_tree.h"

/*******************************************************************\

Function: ansi_c_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_parse_treet::swap(ansi_c_parse_treet &ansi_c_parse_tree)
{
  ansi_c_parse_tree.items.swap(items);
  ansi_c_parse_tree.include_map.swap(include_map);
}

/*******************************************************************\

Function: ansi_c_parse_treet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_parse_treet::clear()
{
  items.clear();
  include_map.clear();
}

/*******************************************************************\

Function: ansi_c_parse_treet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_parse_treet::output(std::ostream &out) const
{
  for(itemst::const_iterator
      it=items.begin();
      it!=items.end();
      it++)
  {
    it->output(out);
    out << "\n";
  }
}
