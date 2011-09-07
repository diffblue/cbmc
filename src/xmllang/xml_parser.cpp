/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>
#include <string.h>

#include <fstream>

#include "xml_parser.h"

xml_parsert xml_parser;

/*******************************************************************\

Function: parse_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// 'do it all' function
bool parse_xml(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  xml_parser.clear();
  xml_parser.filename=filename;
  xml_parser.in=&in;
  xml_parser.set_message_handler(message_handler);

  bool result=yyxmlparse();

  // save result
  xml_parser.parse_tree.element.swap(dest);

  // save some memory
  xml_parser.clear();

  return result;  
}

/*******************************************************************\

Function: parse_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// 'do it all' function
bool parse_xml(
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  std::ifstream in(filename.c_str());
  
  if(!in) return true;
 
  return parse_xml(in, filename, message_handler, dest);
}
