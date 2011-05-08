/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef XML_PARSER_H
#define XML_PARSER_H

#include <parser.h>

#include "xml_parse_tree.h"

int yyxmlparse();

class xml_parsert:public parsert
{
public:
  xml_parse_treet parse_tree;

  std::list<xmlt *> stack;
  
  xmlt &current()
  {
    return *stack.back();
  }
   
  virtual bool parse()
  {
    return yyxmlparse();
  }
  
  void new_level()
  {
    current().elements.push_back(xmlt());
    stack.push_back(&current().elements.back());
  }

  virtual void clear()
  {
    parse_tree.clear();
    // set up stack
    stack.clear();
    stack.push_back(&parse_tree.element);
  }
  
  static std::string unescape(const char *s);
};

extern xml_parsert xml_parser;

int yyxmlerror(const std::string &error);

// 'do it all' function
bool parse_xml(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest);

#endif
