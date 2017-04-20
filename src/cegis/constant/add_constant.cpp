/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/cprover_prefix.h>

#include <ansi-c/expr2c.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>

namespace
{
const char NS_SEP[]="::";
bool is_meta_or_not_global(const symbolt &symbol)
{
  if(ID_code == symbol.type.id()) return true;
  const std::string &name=id2string(symbol.name);
  if(std::string::npos != name.find("#return_value")) return true;
  if(std::string::npos != name.find(CPROVER_PREFIX)) return true;
  return std::string::npos != name.find(NS_SEP);
}

bool contains_constant(const symbol_tablet &st, const exprt &value)
{
  typedef symbol_tablet::symbolst symbolst;
  exprt lhs=value;
  lhs.add_source_location()=source_locationt();
  const symbolst &s=st.symbols;
  for(symbolst::const_iterator it=s.begin(); it != s.end(); ++it)
  {
    const symbolt &symbol=it->second;
    if(is_meta_or_not_global(symbol)) continue;
    exprt rhs=symbol.value;
    rhs.add_source_location()=lhs.source_location();
    if(lhs == rhs) return true;
  }
  return false;
}

bool is_empty(const exprt &expr)
{
  return exprt() == expr;
}
}

void add_cegis_constant(symbol_tablet &st, goto_functionst &gf,
    const std::string &name, const exprt &value, goto_programt::targett pos)
{
  while(is_builtin(pos->source_location))
    ++pos;
  typet type=value.type();
  type.set(ID_C_constant, true);
  create_cegis_symbol(st, name, type).value=value;
  if(!is_empty(value))
    pos=cegis_assign_user_variable(st, gf, pos, name, value);
}

void add_cegis_constant(symbol_tablet &st, goto_functionst &gf,
    const exprt &value, goto_programt::targett pos)
{
  if(contains_constant(st, value)) return;
  const namespacet ns(st);
  std::string name(CEGIS_CONSTANT_PREFIX);
  name+=expr2c(value, ns);
  add_cegis_constant(st, gf, name, value, pos);
}
