/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_PARSE_TREE_H
#define CPROVER_JSIL_JSIL_PARSE_TREE_H

#include <iosfwd>
#include <list>

#include <util/std_code.h>

class symbolt;

class jsil_declarationt:public exprt
{
public:
  jsil_declarationt():exprt(ID_declaration)
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

  void add_returns(
    const irep_idt &value,
    const irep_idt &label)
  {
    add(ID_return).set(ID_value, value);
    add(ID_return).set(ID_label, label);
  }

  const irep_idt &returns_value() const
  {
    return find(ID_return).get(ID_value);
  }

  const irep_idt &returns_label() const
  {
    return find(ID_return).get(ID_label);
  }

  void add_throws(
    const irep_idt &value,
    const irep_idt &label)
  {
    add(ID_throw).set(ID_value, value);
    add(ID_throw).set(ID_label, label);
  }

  const irep_idt &throws_value() const
  {
    return find(ID_throw).get(ID_value);
  }

  const irep_idt &throws_label() const
  {
    return find(ID_throw).get(ID_label);
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

class jsil_parse_treet
{
public:
  typedef std::list<jsil_declarationt> itemst;
  itemst items;

  void swap(jsil_parse_treet &other)
  {
    items.swap(other.items);
  }

  void clear()
  {
    items.clear();
  }

  void output(std::ostream &out) const;
};

#endif // CPROVER_JSIL_JSIL_PARSE_TREE_H
