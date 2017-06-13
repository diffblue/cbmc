/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

/// \file
/// Detection for Uninitialized Local Variables

#include <util/std_expr.h>
#include <util/std_code.h>

#include "uninitialized_domain.h"

void uninitialized_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(has_values.is_false())
    return;

  switch(from->type)
  {
  case DECL:
    {
      const irep_idt &identifier=
        to_code_decl(from->code).get_identifier();
      const symbolt &symbol=ns.lookup(identifier);

      if(!symbol.is_static_lifetime)
        uninitialized.insert(identifier);
    }
    break;

  default:
    {
      std::list<exprt> read=expressions_read(*from);
      std::list<exprt> written=expressions_written(*from);

      forall_expr_list(it, written) assign(*it);

      // we only care about the *first* uninitalized use
      forall_expr_list(it, read) assign(*it);
    }
  }
}

void uninitialized_domaint::assign(const exprt &lhs)
{
  if(lhs.id()==ID_index)
    assign(to_index_expr(lhs).array());
  else if(lhs.id()==ID_member)
    assign(to_member_expr(lhs).struct_op());
  else if(lhs.id()==ID_symbol)
    uninitialized.erase(to_symbol_expr(lhs).get_identifier());
}

void uninitialized_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(has_values.is_known())
    out << has_values.to_string() << '\n';
  else
  {
    for(const auto &id : uninitialized)
      out << id << '\n';
  }
}

/// \return returns true iff there is s.th. new
bool uninitialized_domaint::merge(
  const uninitialized_domaint &other,
  locationt from,
  locationt to)
{
  unsigned old_uninitialized=uninitialized.size();

  uninitialized.insert(
    other.uninitialized.begin(),
    other.uninitialized.end());

  bool changed=
    (has_values.is_false() && !other.has_values.is_false()) ||
    old_uninitialized!=uninitialized.size();
  has_values=tvt::unknown();

  return changed;
}
