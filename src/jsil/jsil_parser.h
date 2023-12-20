/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_PARSER_H
#define CPROVER_JSIL_JSIL_PARSER_H

#include <util/parser.h>

#include "jsil_parse_tree.h"

class jsil_parsert;
int yyjsilparse(jsil_parsert &);
void jsil_scanner_init(jsil_parsert &);

class jsil_parsert:public parsert
{
public:
  explicit jsil_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
  }

  jsil_parse_treet parse_tree;

  virtual bool parse() override
  {
    jsil_scanner_init(*this);
    return yyjsilparse(*this) != 0;
  }

  virtual void clear() override
  {
    parsert::clear();
    parse_tree.clear();

    // scanner state
    string_literal.clear();
  }

  // internal state of the scanner
  std::string string_literal;
};

#endif // CPROVER_JSIL_JSIL_PARSER_H
