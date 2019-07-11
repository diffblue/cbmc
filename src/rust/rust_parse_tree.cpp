/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#include "rust_parse_tree.h"

#include <ostream>

#include <util/symbol.h>

#include "rust_types.h"

void rust_declarationt::to_symbol(symbolt &symbol) const
{
  symbol.clear();

  symbol_exprt s(
    to_symbol_expr(static_cast<const exprt &>(find(ID_declarator))));

  symbol.name = s.get_identifier();
  symbol.base_name = s.get_identifier();
  symbol.mode = "rust";
  symbol.location = s.source_location();
  symbol.type = s.type();

  code_blockt code(to_code_block(static_cast<const codet &>(find(ID_value))));

  symbol.value.swap(code);
}

void rust_declarationt::output(std::ostream &out) const
{
  out << "Declarator: " << find(ID_declarator).pretty() << "\n";
  out << "Value: " << find(ID_value).pretty() << "\n";
}

void rust_parse_treet::output(std::ostream &out) const
{
  for(itemst::const_iterator it = items.begin(); it != items.end(); it++)
  {
    it->output(out);
    out << "\n";
  }
}
