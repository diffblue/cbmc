/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "xml_parser.h"

#include <fstream>

void xml_parser_init(xml_parsert *_xml_parser);
void xml_scanner_init(xml_parsert *_xml_parser);
int yyxmlparse();

bool xml_parsert::parse()
{
  xml_scanner_init(this);
  xml_parser_init(this);
  return yyxmlparse()!=0;
}

void xml_parsert::clear()
{
  parse_tree.clear();
  // set up stack
  stack.clear();
  stack.push_back(&parse_tree.element);
  xml_parser_init(nullptr);
  xml_scanner_init(nullptr);
}

// 'do it all' function
bool parse_xml(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  xml_parsert xml_parser(message_handler);

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
