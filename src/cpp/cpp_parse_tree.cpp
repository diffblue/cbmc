/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "cpp_parse_tree.h"

/*******************************************************************\

Function: cpp_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_parse_treet::swap(cpp_parse_treet &cpp_parse_tree)
{
  cpp_parse_tree.items.swap(items);
}

/*******************************************************************\

Function: cpp_parse_treet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_parse_treet::clear()
{
  items.clear();
}

