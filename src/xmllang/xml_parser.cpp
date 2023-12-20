/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "xml_parser.h"

#include <fstream>

int yyxmlparse(xml_parsert &);

bool xml_parsert::parse()
{
  return yyxmlparse(*this) != 0;
}

// 'do it all' function
bool parse_xml(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  xml_parsert xml_parser{message_handler};

  xml_parser.set_file(filename);
  xml_parser.in=&in;

  bool result = xml_parser.parse();

  // save result
  xml_parser.parse_tree.element.swap(dest);

  // save some memory
  xml_parser.clear();

  return result;
}

// 'do it all' function
bool parse_xml(
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  std::ifstream in(filename);

  if(!in)
    return true;

  return parse_xml(in, filename, message_handler, dest);
}
