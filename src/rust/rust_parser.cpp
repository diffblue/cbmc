/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#include "rust_parser.h"

rust_parsert rust_parser;

extern char const *yyrusttext;

void yyrust::parser::error(const std::string &msg)
{
  rust_parser.parse_error(msg, yyrusttext);
}

void rust_scanner_init()
{
  // TODO: do nothing for now, empty function required for compilation as is
}
