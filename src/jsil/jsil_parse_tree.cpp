/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_parse_tree.h"

#include <ostream>

#include <util/symbol.h>

#include "jsil_types.h"

static bool insert_at_label(
  const codet &code,
  const irep_idt &label,
  code_blockt &dest)
{
  for(auto &c : dest.statements())
  {
    if(c.get_statement()!=ID_label)
      continue;

    code_labelt &l=to_code_label(c);
    if(l.get_label()!=label)
      continue;

    DATA_INVARIANT(l.code().get_statement() == ID_skip, "code should be skip");
    l.code()=code;

    return false;
  }

  return true;
}

symbolt jsil_declarationt::to_symbol() const
{
  symbol_exprt s(to_symbol_expr(
      static_cast<const exprt&>(find(ID_declarator))));

  code_typet symbol_type=to_code_type(s.type());

  irep_idt proc_type=s.get("proc_type");

  if(proc_type=="builtin")
    symbol_type=jsil_builtin_code_typet(symbol_type);
  else if(proc_type=="spec")
    symbol_type=jsil_spec_code_typet(symbol_type);

  symbolt symbol{s.get_identifier(), symbol_type, "jsil"};
  symbol.base_name=s.get_identifier();
  symbol.location=s.source_location();

  code_blockt code(to_code_block(
      static_cast<const codet&>(find(ID_value))));

  irept returns(find(ID_return));
  code_frontend_returnt r(symbol_exprt::typeless(returns.get(ID_value)));

  irept throws(find(ID_throw));
  side_effect_expr_throwt t(
    symbol_exprt::typeless(throws.get(ID_value)), typet(), s.source_location());
  code_expressiont ct(t);

  if(insert_at_label(r, returns.get(ID_label), code))
    throw "return label "+returns.get_string(ID_label)+" not found";
  if(insert_at_label(ct, throws.get(ID_label), code))
    throw "throw label "+throws.get_string(ID_label)+" not found";

  symbol.value.swap(code);

  return symbol;
}

void jsil_declarationt::output(std::ostream &out) const
{
  out << "Declarator: " << find(ID_declarator).pretty() << "\n";
  out << "Returns: " << find(ID_return).pretty() << "\n";
  out << "Throws: " << find(ID_throw).pretty() << "\n";
  out << "Value: " << find(ID_value).pretty() << "\n";
}

void jsil_parse_treet::output(std::ostream &out) const
{
  for(itemst::const_iterator
      it=items.begin();
      it!=items.end();
      it++)
  {
    it->output(out);
    out << "\n";
  }
}
