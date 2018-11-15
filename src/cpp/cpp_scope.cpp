/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_scope.h"

#include "cpp_typecheck.h"

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

  // using scopes
  for(const auto &s_ptr : using_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup_rec(base_name_to_lookup, QUALIFIED, id_set);
  }

  if(!id_set.empty())
    return; // done, upwards scopes are hidden

  // secondary scopes
  for(const auto &s_ptr : secondary_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup_rec(base_name_to_lookup, QUALIFIED, id_set);
  }

  if(kind==QUALIFIED)
    return; // done

  if(!id_set.empty())
    return; // done

  // ask parent, recursive call
  if(!is_root_scope())
    get_parent().lookup_rec(base_name_to_lookup, kind, id_set);
}

void cpp_scopet::lookup_rec(
  const irep_idt &base_name_to_lookup,
  lookup_kindt kind,
  cpp_idt::id_classt identifier_class,
  id_sett &id_set)
{
  // we have a hack to do full search in case we
  // are looking for templates!

  #if 0
  std::cout << "B: " << base_name_to_lookup << '\n';
  std::cout << "K: " << kind << '\n';
  std::cout << "I: " << identifier_class << '\n';
  std::cout << "THIS: " << base_name << " " << identifier_class
            << " " << this->identifier << '\n';
  #endif

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

  // using scopes
  for(const auto &s_ptr : using_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup_rec(
      base_name_to_lookup, QUALIFIED, identifier_class, id_set);
  }

  if(!id_set.empty() && identifier_class != id_classt::TEMPLATE)
    return; // done, upwards scopes are hidden

  // secondary scopes
  for(const auto &s_ptr : secondary_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup_rec(
      base_name_to_lookup, QUALIFIED, identifier_class, id_set);
  }

  if(kind==QUALIFIED)
    return; // done

  if(!id_set.empty() && identifier_class != id_classt::TEMPLATE)
    return; // done, upwards scopes are hidden

  // ask parent, recursive call
  if(!is_root_scope())
    get_parent().lookup_rec(
      base_name_to_lookup, kind, identifier_class, id_set);
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
