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

int yyjsilparse();

class jsil_parsert:public parsert
{
public:
  jsil_parse_treet parse_tree;

  virtual bool parse() override
  {
    return yyjsilparse()!=0;
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

extern jsil_parsert jsil_parser;

int yyjsilerror(const std::string &error);
void jsil_scanner_init();

#endif // CPROVER_JSIL_JSIL_PARSER_H
