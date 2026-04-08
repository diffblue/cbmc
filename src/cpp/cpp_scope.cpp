/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_scope.h"

std::ostream &operator << (std::ostream &out, cpp_scopet::lookup_kindt kind)
{
  switch(kind)
  {
  case cpp_scopet::QUALIFIED: return out << "QUALIFIED";
  case cpp_scopet::SCOPE_ONLY: return out << "SCOPE_ONLY";
  case cpp_scopet::RECURSIVE: return out << "RECURSIVE";
  default: UNREACHABLE;
  }

  return out;
}

void cpp_scopet::lookup_rec(
  const irep_idt &base_name_to_lookup,
  lookup_kindt kind,
  id_sett &id_set)
{
  visited_sett visited;
  lookup_rec(base_name_to_lookup, kind, id_set, visited);
}

void cpp_scopet::lookup_rec(
  const irep_idt &base_name_to_lookup,
  lookup_kindt kind,
  id_sett &id_set,
  visited_sett &visited)
{
  // Track visited scopes to prevent redundant traversals through
  // using_scopes and secondary_scopes. For QUALIFIED lookups (entered
  // via using/secondary scopes), skip entirely if already visited.
  // For RECURSIVE lookups (walking up to parent), still check this
  // scope's own members but skip its using/secondary scopes if already
  // visited — the parent traversal needs to proceed regardless.
  bool already_visited = !visited.insert(this).second;
  if(already_visited && kind == QUALIFIED)
    return;

  cpp_id_mapt::iterator lower_it = sub.lower_bound(base_name_to_lookup);

  if(lower_it!=sub.end())
  {
    cpp_id_mapt::iterator upper_it = sub.upper_bound(base_name_to_lookup);

    for(cpp_id_mapt::iterator n_it=lower_it;
        n_it!=upper_it; n_it++)
      id_set.insert(&n_it->second);
  }

  if(base_name == base_name_to_lookup)
    id_set.insert(this);

  if(kind==SCOPE_ONLY)
    return; // done

  if(!already_visited)
  {
    // using scopes
    for(const auto &s_ptr : using_scopes)
    {
      cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);
      other_scope.lookup_rec(base_name_to_lookup, QUALIFIED, id_set, visited);
    }

    if(!id_set.empty())
      return; // done, upwards scopes are hidden

    // secondary scopes
    for(const auto &s_ptr : secondary_scopes)
    {
      cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);
      other_scope.lookup_rec(base_name_to_lookup, QUALIFIED, id_set, visited);
    }
  }

  if(kind==QUALIFIED)
    return; // done

  if(!id_set.empty())
    return; // done

  // ask parent, recursive call
  if(!is_root_scope())
    get_parent().lookup_rec(base_name_to_lookup, kind, id_set, visited);
}

void cpp_scopet::lookup_rec(
  const irep_idt &base_name_to_lookup,
  lookup_kindt kind,
  cpp_idt::id_classt identifier_class,
  id_sett &id_set)
{
  visited_sett visited;
  lookup_rec(base_name_to_lookup, kind, identifier_class, id_set, visited);
}

void cpp_scopet::lookup_rec(
  const irep_idt &base_name_to_lookup,
  lookup_kindt kind,
  cpp_idt::id_classt identifier_class,
  id_sett &id_set,
  visited_sett &visited)
{
  bool already_visited = !visited.insert(this).second;
  if(already_visited && kind == QUALIFIED)
    return;

  cpp_id_mapt::iterator lower_it = sub.lower_bound(base_name_to_lookup);

  if(lower_it!=sub.end())
  {
    cpp_id_mapt::iterator upper_it = sub.upper_bound(base_name_to_lookup);

    for(cpp_id_mapt::iterator n_it=lower_it;
        n_it!=upper_it; n_it++)
    {
      if(n_it->second.id_class == identifier_class)
        id_set.insert(&n_it->second);
    }
  }

  if(base_name == base_name_to_lookup && id_class == identifier_class)
    id_set.insert(this);

  if(kind==SCOPE_ONLY)
    return; // done

  if(!already_visited)
  {
    // using scopes
    for(const auto &s_ptr : using_scopes)
    {
      cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);
      other_scope.lookup_rec(
        base_name_to_lookup, QUALIFIED, identifier_class, id_set, visited);
    }

    if(!id_set.empty() && identifier_class != id_classt::TEMPLATE)
      return; // done, upwards scopes are hidden

    // secondary scopes
    for(const auto &s_ptr : secondary_scopes)
    {
      cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);
      other_scope.lookup_rec(
        base_name_to_lookup, QUALIFIED, identifier_class, id_set, visited);
    }
  }

  if(kind==QUALIFIED)
    return; // done

  if(!id_set.empty() && identifier_class != id_classt::TEMPLATE)
    return; // done, upwards scopes are hidden

  // ask parent, recursive call
  if(!is_root_scope())
    get_parent().lookup_rec(
      base_name_to_lookup, kind, identifier_class, id_set, visited);
}

cpp_scopet::id_sett cpp_scopet::lookup_identifier(
  const irep_idt &id,
  cpp_idt::id_classt identifier_class)
{
  id_sett id_set;

  for(cpp_id_mapt::iterator n_it=sub.begin();
      n_it!=sub.end(); n_it++)
  {
    if(
      n_it->second.identifier == id &&
      n_it->second.id_class == identifier_class)
    {
      id_set.insert(&n_it->second);
    }
  }

  if(identifier == id && id_class == identifier_class)
    id_set.insert(this);

  #if 0
  for(std::size_t i=0; i<parents_size(); i++)
  {
    cpp_idt &parent= get_parent(i);
    if(parent.identifier == id
       && parent.id_class == identifier_class)
        id_set.insert(&parent);
  }
  #endif

  return id_set;
}

cpp_scopet &cpp_scopet::new_scope(const irep_idt &new_scope_name)
{
  cpp_idt &id=insert(new_scope_name);
  id.identifier=prefix+id2string(new_scope_name);
  id.prefix=prefix+id2string(new_scope_name)+"::";
  id.this_expr=this_expr;
  id.class_identifier=class_identifier;
  id.is_scope=true;
  return (cpp_scopet &)id;
}

bool cpp_scopet::contains(const irep_idt &base_name_to_lookup)
{
  return !lookup(base_name_to_lookup, SCOPE_ONLY).empty();
}
