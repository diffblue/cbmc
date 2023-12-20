/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_XMLLANG_XML_PARSER_H
#define CPROVER_XMLLANG_XML_PARSER_H

#include <util/parser.h>

#include "xml_parse_tree.h"

class xml_parsert:public parsert
{
public:
  explicit xml_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
    stack.push_back(&parse_tree.element);
  }

  xml_parse_treet parse_tree;

  std::list<xmlt *> stack;

  xmlt &current()
  {
    return *stack.back();
  }

  bool parse() override;

  void new_level()
  {
    current().elements.push_back(xmlt());
    stack.push_back(&current().elements.back());
  }

  void clear() override
  {
    parse_tree.clear();
    // set up stack
    stack.clear();
    stack.push_back(&parse_tree.element);
  }
};

int yyxmlerror(xml_parsert &xml_parser, const std::string &error);

// 'do it all' functions
bool parse_xml(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest);

bool parse_xml(
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest);

#endif // CPROVER_XMLLANG_XML_PARSER_H
