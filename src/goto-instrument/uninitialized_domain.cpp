/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

#include <std_expr.h>
#include <std_code.h>

#include "uninitialized_domain.h"

/*******************************************************************\

Function: uninitialized_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uninitialized_domaint::transform(
  const namespacet &ns,
  locationt from,
  locationt to)
{
  switch(from->type)
  {
  case DECL:
    {
      const irep_idt &identifier=
        to_code_decl(from->code).get_identifier();
      const symbolt &symbol=ns.lookup(identifier);

      if(!symbol.static_lifetime)
        uninitialized.insert(identifier);
    }
    break;

  default:
    {
      std::list<exprt> read=expressions_read(*from);
      std::list<exprt> written=expressions_written(*from);

      forall_expr_list(it, read) find_dirty(ns, *it);
      forall_expr_list(it, written) assign(*it);
      
      // we only care about the *first* uninitalized use
      forall_expr_list(it, read) assign(*it);
    }
  }
}

/*******************************************************************\

Function: uninitialized_domaint::find_dirty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uninitialized_domaint::find_dirty(
  const namespacet &ns,
  const exprt &expr)
{
  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);
    if(address_of_expr.object().id()==ID_symbol)
    {
      const irep_idt &identifier=
        to_symbol_expr(address_of_expr.object()).get_identifier();
      const symbolt &symbol=ns.lookup(identifier);
      if(!symbol.static_lifetime) dirty.insert(identifier);
    }
  }
  
  forall_operands(it, expr)
    find_dirty(ns, *it);
}

/*******************************************************************\

Function: uninitialized_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uninitialized_domaint::assign(const exprt &lhs)
{
  if(lhs.id()==ID_index)
    assign(to_index_expr(lhs).array());
  else if(lhs.id()==ID_member)
    assign(to_member_expr(lhs).struct_op());
  else if(lhs.id()==ID_symbol)
    uninitialized.erase(to_symbol_expr(lhs).get_identifier());
}

/*******************************************************************\

Function: uninitialized_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uninitialized_domaint::output(
  const namespacet &ns,
  std::ostream &out) const
{
  out << "Uninitialized:" << std::endl;
  for(uninitializedt::const_iterator
      it=uninitialized.begin();
      it!=uninitialized.end();
      it++)
    out << "  " << *it << std::endl;

  out << "Dirty:" << std::endl;
  for(dirtyt::const_iterator
      it=dirty.begin();
      it!=dirty.end();
      it++)
    out << "  " << *it << std::endl;
}

/*******************************************************************\

Function: uninitialized_domaint::merge

  Inputs:

 Outputs: returns true iff there is s.th. new

 Purpose:

\*******************************************************************/

bool uninitialized_domaint::merge(const uninitialized_domaint &other)
{
  unsigned old_uninitialized=uninitialized.size();
  unsigned old_dirty=dirty.size();
  
  uninitialized.insert(
    other.uninitialized.begin(),
    other.uninitialized.end());

  dirty.insert(other.dirty.begin(), other.dirty.end());
    
  return old_uninitialized!=uninitialized.size() ||
         old_dirty!=dirty.size();
}
