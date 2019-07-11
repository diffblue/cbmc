/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/

/// \file
/// Rust Language

#ifndef CPROVER_RUST_RUST_PARSE_TREE_H
#define CPROVER_RUST_RUST_PARSE_TREE_H

#include <iosfwd>
#include <list>

#include <util/std_code.h>
#include <util/std_expr.h>

class symbolt;

class rust_declarationt : public exprt
{
public:
  rust_declarationt() : exprt(ID_declaration)
  {
  }

  void add_declarator(const symbol_exprt &expr)
  {
    add(ID_declarator, expr);
  }

  const symbol_exprt &declarator() const
  {
    return static_cast<const symbol_exprt &>(find(ID_declarator));
  }

  symbol_exprt &declarator()
  {
    return static_cast<symbol_exprt &>(add(ID_declarator));
  }

  void add_value(const code_blockt &code)
  {
    add(ID_value, code);
  }

  const code_blockt &value() const
  {
    return static_cast<const code_blockt &>(find(ID_value));
  }

  code_blockt &value()
  {
    return static_cast<code_blockt &>(add(ID_value));
  }

  void to_symbol(symbolt &symbol) const;

  void output(std::ostream &) const;
};

class rust_parse_treet
{
public:
  typedef std::list<rust_declarationt> itemst;
  itemst items;

  void swap(rust_parse_treet &other)
  {
    items.swap(other.items);
  }

  void clear()
  {
    items.clear();
  }

  void output(std::ostream &out) const;
};

#endif // CPROVER_RUST_RUST_PARSE_TREE_H
