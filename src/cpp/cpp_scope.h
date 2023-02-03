/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_SCOPE_H
#define CPROVER_CPP_CPP_SCOPE_H

#include <iosfwd>
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

  id_sett lookup(const irep_idt &base_name_to_lookup, lookup_kindt kind)
  {
    id_sett result;
    lookup_rec(base_name_to_lookup, kind, result);
    return result;
  }

  id_sett lookup(
    const irep_idt &base_name_to_lookup,
    lookup_kindt kind,
    cpp_idt::id_classt identifier_class)
  {
    id_sett result;
    lookup_rec(base_name_to_lookup, kind, identifier_class, result);
    return result;
  }

  id_sett
  lookup_identifier(const irep_idt &id, cpp_idt::id_classt identifier_class);

  cpp_idt &insert(const irep_idt &_base_name)
  {
    cpp_id_mapt::iterator it=
      sub.insert(std::pair<irep_idt, cpp_idt>
        (_base_name, cpp_idt()));

    it->second.base_name=_base_name;
    it->second.set_parent(*this);

    return it->second;
  }

  cpp_idt &insert(const cpp_idt &cpp_id)
  {
    cpp_id_mapt::iterator it=
      sub.insert(std::pair<irep_idt, cpp_idt>
        (cpp_id.base_name, cpp_id));

    it->second.set_parent(*this);

    return it->second;
  }

  bool contains(const irep_idt &base_name_to_lookup);

  bool is_root_scope() const
  {
    return id_class==id_classt::ROOT_SCOPE;
  }

  bool is_global_scope() const
  {
    return id_class==id_classt::ROOT_SCOPE ||
           id_class==id_classt::NAMESPACE;
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
    PRECONDITION(other.is_scope);
    secondary_scopes.push_back(&other);
  }

  void add_using_scope(cpp_scopet &other)
  {
    PRECONDITION(other.is_scope);
    using_scopes.push_back(&other);
  }

  class cpp_scopet &new_scope(const irep_idt &new_scope_name);

protected:
  void lookup_rec(const irep_idt &base_name, lookup_kindt kind, id_sett &);

  void lookup_rec(
    const irep_idt &base_name,
    lookup_kindt kind,
    cpp_idt::id_classt id_class,
    id_sett &);
};

class cpp_root_scopet:public cpp_scopet
{
public:
  cpp_root_scopet()
  {
    id_class=id_classt::ROOT_SCOPE;
    identifier="::";
  }
};

std::ostream &operator << (std::ostream &out, cpp_scopet::lookup_kindt);

#endif // CPROVER_CPP_CPP_SCOPE_H
