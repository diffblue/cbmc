/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_PARSE_TREE_H
#define CPROVER_XML_PARSE_TREE_H

#include "xml.h"

class xml_parse_treet
{
public:
  xmlt xml;
  xmlt element;

  void swap(xml_parse_treet &xml_parse_tree);
  void clear();
};

#endif
