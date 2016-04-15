/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#ifndef CPROVER_JSIL_PARSE_TREE_H
#define CPROVER_JSIL_PARSE_TREE_H

#include <ostream>
#include <list>

#include <util/std_expr.h>
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

  void add_returns(
    const irep_idt &value,
    const irep_idt &label)
  {
    add(ID_return).set(ID_value, value);
    add(ID_return).set(ID_label, label);
  }

  void add_throws(
    const irep_idt &value,
    const irep_idt &label)
  {
    add(ID_throw).set(ID_value, value);
    add(ID_throw).set(ID_label, label);
  }

  void add_value(const code_blockt &code)
  {
    add(ID_value, code);
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

#endif
