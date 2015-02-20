/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef JSON_PARSER_H
#define JSON_PARSER_H

#include <cassert>
#include <stack>

#include <util/parser.h>

#include "json.h"

int yyjsonparse();

class json_parsert:public parsert
{
public:
  typedef std::stack<jsont, std::vector<jsont> > stackt;
  stackt stack;
  
  inline jsont &top() { return stack.top(); }
  
  inline void push(const jsont &x)
  {
    stack.push(x);
  }

  inline void pop(jsont &dest)
  {
    assert(!stack.empty());
    dest.swap(stack.top());
    stack.pop();
  }

  virtual void clear()
  {
    stack=stackt();
  }
};

extern json_parsert json_parser;

int yyjsonerror(const std::string &error);

// 'do it all' functions
bool parse_json(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest);

bool parse_json(
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest);

#endif
