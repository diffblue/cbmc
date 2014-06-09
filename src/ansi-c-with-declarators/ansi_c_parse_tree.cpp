/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
    symbolt tmp;
    it->to_symbol(tmp);
    out << tmp;
  }
}
