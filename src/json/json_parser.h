/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JSON_JSON_PARSER_H
#define CPROVER_JSON_JSON_PARSER_H

#include <stack>

#include <util/parser.h>
#include <util/json.h>

int yyjsonparse();
void yyjsonrestart(FILE *input_file);

class json_parsert:public parsert
{
public:
  typedef std::stack<jsont, std::vector<jsont> > stackt;
  stackt stack;

  jsont &top() { return stack.top(); }

  virtual bool parse() override
  {
    return yyjsonparse()!=0;
  }

  void push(const jsont &x)
  {
    stack.push(x);
  }

  void pop(jsont &dest)
  {
    assert(!stack.empty());
    dest.swap(stack.top());
    stack.pop();
  }

  virtual void clear() override
  {
    stack=stackt();
    yyjsonrestart(nullptr);
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

#endif // CPROVER_JSON_JSON_PARSER_H
