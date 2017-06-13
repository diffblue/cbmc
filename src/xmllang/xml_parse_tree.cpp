/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "xml_parse_tree.h"

/*******************************************************************\

Function: xml_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_parse_treet::swap(xml_parse_treet &xml_parse_tree)
{
  xml_parse_tree.element.swap(element);
}

/*******************************************************************\

Function: xml_parse_treet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_parse_treet::clear()
{
  xml.clear();
  element.clear();
}
