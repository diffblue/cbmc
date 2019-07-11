/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/

/// \file
/// Rust Language

#ifndef CPROVER_RUST_RUST_PARSER_H
#define CPROVER_RUST_RUST_PARSER_H

#include <util/parser.h>

#include "rust_parse_tree.h"
#include "rust_y.tab.h"

class rust_parsert : public parsert
{
public:
  rust_parse_treet parse_tree;

  bool parse() override
  {
    yyrust::parser parser;
    // TODO Debug Turn off debug output
    // parser.set_debug_level(1);
    return parser.parse() != 0;
  }

  void clear() override
  {
    parsert::clear();
    parse_tree.clear();

    // scanner state
    string_literal.clear();
  }

  // internal state of the scanner
  std::string string_literal;
};

extern rust_parsert rust_parser;

int yyrusterror(const std::string &error);
void yyrusterror(char const *error);

void rust_scanner_init();

#endif // CPROVER_RUST_RUST_PARSER_H
