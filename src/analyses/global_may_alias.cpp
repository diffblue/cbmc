/*******************************************************************\

Module: Field-insensitive, location-sensitive global may alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive global may alias analysis

#include "global_may_alias.h"

#include <util/pointer_expr.h>

/// Populate list of aliases for a given identifier in a context in
/// which an object is being written to.
/// \param lhs: A left hand side expression, containing an identifier.
/// \param alias_set: An external set of aliases to populate internal
///   aliases set.
void global_may_alias_domaint::assign_lhs_aliases(
  const exprt &lhs,
  const std::set<irep_idt> &alias_set)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();

    aliases.isolate(identifier);

    for(const auto &alias : alias_set)
    {
      aliases.make_union(identifier, alias);
    }
  }
}

/// Populate list of aliases for a given identifier in a context in
/// which is an object is being read.
/// \param rhs: A right hand side expression.
/// \param alias_set: A external set of aliases to populate internal
///   aliases set.
void global_may_alias_domaint::get_rhs_aliases(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    alias_set.insert(identifier);

    for(const auto &alias : alias_set)
      if(aliases.same_set(alias, identifier))
        alias_set.insert(alias);
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
    get_rhs_aliases_address_of(to_address_of_expr(rhs).object(), alias_set);
  }
}

/// Specialisation of \ref global_may_alias_domaint::get_rhs_aliases
/// to deal with address_of expressions.
/// \param rhs: A right hand side expression.
/// \param alias_set: A external set of aliases to populate internal
///   aliases set.
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

void global_may_alias_domaint::transform(
  const irep_idt &function_from,
  trace_ptrt trace_from,
  const irep_idt &function_to,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};

  if(has_values.is_false())
    return;

  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type())
  {
  case ASSIGN:
  {
    std::set<irep_idt> rhs_aliases;
    get_rhs_aliases(instruction.assign_rhs(), rhs_aliases);
    assign_lhs_aliases(instruction.assign_lhs(), rhs_aliases);
    break;
  }

  case DECL:
    aliases.isolate(instruction.decl_symbol().get_identifier());
    break;

  case DEAD:
    aliases.isolate(instruction.dead_symbol().get_identifier());
    break;

  case FUNCTION_CALL: // Probably safe
  case GOTO:          // Ignoring the guard is a valid over-approximation
    break;
  case CATCH:
  case THROW:
    DATA_INVARIANT(false, "Exceptions must be removed before analysis");
    break;
  case SET_RETURN_VALUE:
    DATA_INVARIANT(false, "SET_RETURN_VALUE must be removed before analysis");
    break;
  case ATOMIC_BEGIN: // Ignoring is a valid over-approximation
  case ATOMIC_END:   // Ignoring is a valid over-approximation
  case LOCATION:     // No action required
  case START_THREAD: // Require a concurrent analysis at higher level
  case END_THREAD:   // Require a concurrent analysis at higher level
  case ASSERT:       // No action required
  case ASSUME:       // Ignoring is a valid over-approximation
  case SKIP:         // No action required
  case END_FUNCTION: // No action required
    break;
  case OTHER:
    DATA_INVARIANT(false, "Unclear what is a safe over-approximation of OTHER");
    break;
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    DATA_INVARIANT(false, "Only complete instructions can be analyzed");
    break;
  }
}

void global_may_alias_domaint::output(
  std::ostream &out,
  const ai_baset &,
  const namespacet &) const
{
  if(has_values.is_known())
  {
    out << has_values.to_string() << '\n';
    return;
  }

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
        if(first)
        {
          out << "Aliases: " << *a_it1;
          first=false;
        }
        out << ' ' << *a_it2;
      }
    }

    if(!first)
      out << '\n';
  }
}

bool global_may_alias_domaint::merge(
  const global_may_alias_domaint &b,
  trace_ptrt,
  trace_ptrt)
{
  bool changed=has_values.is_false();
  has_values=tvt::unknown();

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
