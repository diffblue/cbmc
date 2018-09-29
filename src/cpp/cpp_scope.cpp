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

void cpp_scopet::lookup(
  const irep_idt &base_name,
  lookup_kindt kind,
  id_sett &id_set)
{
  cpp_id_mapt::iterator
    lower_it=sub.lower_bound(base_name);

  if(lower_it!=sub.end())
  {
    cpp_id_mapt::iterator
      upper_it=sub.upper_bound(base_name);

    for(cpp_id_mapt::iterator n_it=lower_it;
        n_it!=upper_it; n_it++)
      id_set.insert(&n_it->second);
  }

  if(this->base_name==base_name)
    id_set.insert(this);

  if(kind==SCOPE_ONLY)
    return; // done

  // using scopes
  for(const auto &s_ptr : using_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup(base_name, QUALIFIED, id_set);
  }

  if(!id_set.empty())
    return; // done, upwards scopes are hidden

  // secondary scopes
  for(const auto &s_ptr : secondary_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup(base_name, QUALIFIED, id_set);
  }

  if(kind==QUALIFIED)
    return; // done
  if(!id_set.empty())
    return; // done

  // ask parent, recursive call
  if(!is_root_scope())
    get_parent().lookup(base_name, kind, id_set);
}

void cpp_scopet::lookup(
  const irep_idt &base_name,
  lookup_kindt kind,
  cpp_idt::id_classt id_class,
  id_sett &id_set)
{
  // we have a hack to do full search in case we
  // are looking for templates!

  #if 0
  std::cout << "B: " << base_name << '\n';
  std::cout << "K: " << kind << '\n';
  std::cout << "I: " << id_class << '\n';
  std::cout << "THIS: " << this->base_name << " " << this->id_class
            << " " << this->identifier << '\n';
  #endif

  cpp_id_mapt::iterator
    lower_it=sub.lower_bound(base_name);

  if(lower_it!=sub.end())
  {
    cpp_id_mapt::iterator
      upper_it=sub.upper_bound(base_name);

    for(cpp_id_mapt::iterator n_it=lower_it;
        n_it!=upper_it; n_it++)
    {
      if(n_it->second.id_class == id_class)
        id_set.insert(&n_it->second);
    }
  }

  if(this->base_name == base_name &&
     this->id_class == id_class)
    id_set.insert(this);

  if(kind==SCOPE_ONLY)
    return; // done

  // using scopes
  for(const auto &s_ptr : using_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup(base_name, QUALIFIED, id_class, id_set);
  }

  if(!id_set.empty() && id_class != id_classt::TEMPLATE)
    return; // done, upwards scopes are hidden

  // secondary scopes
  for(const auto &s_ptr : secondary_scopes)
  {
    cpp_scopet &other_scope = static_cast<cpp_scopet &>(*s_ptr);

    // Recursive call.
    // Note the different kind!
    other_scope.lookup(base_name, QUALIFIED, id_class, id_set);
  }

  if(kind==QUALIFIED)
    return; // done

  if(!id_set.empty() &&
     id_class!=id_classt::TEMPLATE) return; // done, upwards scopes are hidden

  // ask parent, recursive call
  if(!is_root_scope())
    get_parent().lookup(base_name, kind, id_class, id_set);
}

void cpp_scopet::lookup_identifier(
  const irep_idt &identifier,
  cpp_idt::id_classt id_class,
  id_sett &id_set)
{
  for(cpp_id_mapt::iterator n_it=sub.begin();
      n_it!=sub.end(); n_it++)
  {
    if(n_it->second.identifier == identifier
       && n_it->second.id_class == id_class)
          id_set.insert(&n_it->second);
  }

  if(this->identifier == identifier
     && this->id_class == id_class)
    id_set.insert(this);

  #if 0
  for(std::size_t i=0; i<parents_size(); i++)
  {
    cpp_idt &parent= get_parent(i);
    if(parent.identifier == identifier
       && parent.id_class == id_class)
        id_set.insert(&parent);
  }
  #endif
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


bool cpp_scopet::contains(const irep_idt &base_name)
{
  id_sett id_set;
  lookup(base_name, SCOPE_ONLY, id_set);
  return !id_set.empty();
}
