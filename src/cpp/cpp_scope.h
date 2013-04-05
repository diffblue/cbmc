/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_SCOPE_H
#define CPROVER_CPP_SCOPE_H

#include <ostream>
#include <set>

#include "cpp_id.h"

class cpp_scopet:public cpp_idt
{
public:
  cpp_scopet()
  {
    is_scope=true;
  }

  typedef std::set<cpp_idt *> id_sett;
  
  enum lookup_kindt { SCOPE_ONLY, QUALIFIED, RECURSIVE };
  
  void lookup(
    const irep_idt &base_name,
    lookup_kindt kind,
    id_sett &id_set);

  void lookup(
    const irep_idt &base_name,
    lookup_kindt kind,
    cpp_idt::id_classt id_class,
    id_sett &id_set);

  void lookup_identifier(
    const irep_idt &identifier,
    cpp_idt::id_classt id_class,
    id_sett &id_set);

  bool contains(const irep_idt &base_name);

  bool is_root_scope() const
  {
    return id_class==ROOT_SCOPE;
  }

  bool is_global_scope() const
  {
    return id_class==ROOT_SCOPE ||
           id_class==NAMESPACE;
  }

  cpp_scopet &get_parent() const
  {
    return static_cast<cpp_scopet &>(cpp_idt::get_parent());
  }
  
  cpp_scopet &get_global_scope()
  {
    cpp_scopet *p=this;
    
    while(!p->is_global_scope())
      p=&(p->get_parent());
    
    return *p;
  }

  void add_secondary_scope(cpp_scopet &other)
  {
    assert(other.is_scope);
    secondary_scopes.push_back(&other);
  }

  void add_using_scope(cpp_scopet &other)
  {
    assert(other.is_scope);
    using_scopes.push_back(&other);
  }

  class cpp_scopet &new_scope(
    const irep_idt &new_scope_name);
};

class cpp_root_scopet:public cpp_scopet
{
public:
  cpp_root_scopet()
  {
    id_class=ROOT_SCOPE;
    identifier="::";
  }
};

std::ostream &operator << (std::ostream &out, cpp_scopet::lookup_kindt);

#endif
