/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "xml_parser.h"

#include <fstream>

int xml_parsert::instance_count = 0;

int yyxmllex_init_extra(xml_parsert *, void **);
int yyxmllex_destroy(void *);
int yyxmlparse(xml_parsert &, void *);

bool xml_parsert::parse()
{
  void *scanner;
  yyxmllex_init_extra(this, &scanner);
  bool parse_fail = yyxmlparse(*this, scanner) != 0;
  yyxmllex_destroy(scanner);
  return parse_fail;
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
