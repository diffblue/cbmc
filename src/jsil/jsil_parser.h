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

class jsil_parsert:public parsert
{
public:
  explicit jsil_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
  }

  jsil_parse_treet parse_tree;

  bool parse() override;

  void clear() override;

  // internal state of the scanner
  std::string string_literal;
};

#endif // CPROVER_JSIL_JSIL_PARSER_H
