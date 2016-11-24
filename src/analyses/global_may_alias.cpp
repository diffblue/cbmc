/*******************************************************************\

Module: Field-insensitive, location-sensitive gobal may alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "global_may_alias.h"

/*******************************************************************\

Function: global_may_alias_domaint::assign_lhs_aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void global_may_alias_domaint::assign_lhs_aliases(
  const exprt &lhs,
  const std::set<irep_idt> &alias_set)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();

    aliases.isolate(identifier);

    for(std::set<irep_idt>::const_iterator it=alias_set.begin();
        it!=alias_set.end();
        it++)
    {
      aliases.make_union(identifier, *it);
    }
  }
}

/*******************************************************************\

Function: global_may_alias_domaint::get_rhs_aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void global_may_alias_domaint::get_rhs_aliases(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    alias_set.insert(identifier);
    
    for(aliasest::const_iterator it=aliases.begin();
        it!=aliases.end();
        it++)
      if(aliases.same_set(*it, identifier))
        alias_set.insert(*it);
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs_aliases(to_if_expr(rhs).true_case(), alias_set);
    get_rhs_aliases(to_if_expr(rhs).false_case(), alias_set);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rhs_aliases(to_typecast_expr(rhs).op(), alias_set);
  }
  else if(rhs.id()==ID_address_of)
  {
    get_rhs_aliases_address_of(to_address_of_expr(rhs).op0(), alias_set);
  }
}

/*******************************************************************\

Function: global_may_alias_domaint::get_rhs_aliases_address_of

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void global_may_alias_domaint::get_rhs_aliases_address_of(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    alias_set.insert("&"+id2string(identifier));
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs_aliases_address_of(to_if_expr(rhs).true_case(), alias_set);
    get_rhs_aliases_address_of(to_if_expr(rhs).false_case(), alias_set);
  }
  else if(rhs.id()==ID_dereference)
  {
  }
}

/*******************************************************************\

Function: global_may_alias_domaint::transform

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void global_may_alias_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);
      
      std::set<irep_idt> aliases;
      get_rhs_aliases(code_assign.rhs(), aliases);
      assign_lhs_aliases(code_assign.lhs(), aliases);
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      aliases.isolate(code_decl.get_identifier());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      aliases.isolate(code_dead.get_identifier());
    }
    break;

  default:;
  }
}

/*******************************************************************\

Function: global_may_alias_domaint::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void global_may_alias_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  for(aliasest::const_iterator a_it1=aliases.begin();
      a_it1!=aliases.end();
      a_it1++)
  {
    bool first=true;
  
    for(aliasest::const_iterator a_it2=aliases.begin();
        a_it2!=aliases.end();
        a_it2++)
    {
      if(aliases.is_root(a_it1) && a_it1!=a_it2 &&
         aliases.same_set(a_it1, a_it2))
      {
        if(first) { out << "Aliases: " << *a_it1; first=false; }
        out << ' ' << *a_it2;
      }
    }

    if(!first) out << '\n';
  }
}

/*******************************************************************\

Function: global_may_alias_domaint::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool global_may_alias_domaint::merge(
  const global_may_alias_domaint &b,
  locationt from,
  locationt to)
{
  bool changed=false;

  // do union
  for(aliasest::const_iterator it=b.aliases.begin();
      it!=b.aliases.end(); it++)
  {
    irep_idt b_root=b.aliases.find(it);
    
    if(!aliases.same_set(*it, b_root))
    {
      aliases.make_union(*it, b_root);
      changed=true;
    }
  }

  // isolate non-tracked ones
  #if 0
  for(aliasest::const_iterator it=aliases.begin();
      it!=aliases.end(); it++)
  {
    if(cleanup_map.find(*it)==cleanup_map.end())
      aliases.isolate(it);
  }
  #endif
  
  return changed;
}
