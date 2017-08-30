/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "xml_parse_tree.h"

void xml_parse_treet::swap(xml_parse_treet &xml_parse_tree)
{
  xml_parse_tree.element.swap(element);
}

void xml_parse_treet::clear()
{
  xml.clear();
  element.clear();
}
