/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_ID_H
#define CPROVER_CPP_ID_H

#include <cassert>
#include <list>
#include <map>
#include <string>
#include <set>
#include <ostream>

#include <util/expr.h>
#include <util/std_types.h>

typedef std::multimap<irep_idt, class cpp_idt> cpp_id_mapt;

class cpp_scopet;

class cpp_idt
{
public:
  cpp_idt();

  typedef enum
  {
    UNKNOWN, SYMBOL, TYPEDEF, CLASS, ENUM, TEMPLATE,
    TEMPLATE_ARGUMENT, NAMESPACE, BLOCK_SCOPE,
    TEMPLATE_SCOPE, ROOT_SCOPE
  } id_classt;

  bool is_member, is_method, is_static_member,
       is_scope, is_constructor;

  id_classt id_class;

  inline bool is_class() const
  {
    return id_class==CLASS;
  }

  inline bool is_enum() const
  {
    return id_class==ENUM;
  }

  inline bool is_namespace() const
  {
    return id_class==NAMESPACE;
  }

  inline bool is_typedef() const
  {
    return id_class==TYPEDEF;
  }

  irep_idt identifier, base_name;

  // if it is a member or method, what class is it in?
  irep_idt class_identifier;
  exprt this_expr;

  // scope data
  std::string prefix;
  unsigned compound_counter;
  
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

  inline cpp_idt &get_parent() const
  {
    assert(parent!=NULL);
    return *parent;
  }

  inline void set_parent(cpp_idt &_parent)
  {
    assert(_parent.is_scope);
    parent=&_parent;
  }

  inline void clear()
  {
    *this=cpp_idt();
  }

  void print(std::ostream &out, unsigned indent=0) const;
  void print_fields(std::ostream &out, unsigned indent=0) const;

  friend class cpp_scopet;

protected:
  cpp_id_mapt sub;

private:
  // These are used for base classes and 'using' clauses.
  typedef std::vector<cpp_idt *> scope_listt;
  scope_listt using_scopes, secondary_scopes;
  cpp_idt *parent;
};

std::ostream &operator<<(std::ostream &out, const cpp_idt &cpp_id);
std::ostream &operator<<(std::ostream &out, const cpp_idt::id_classt &id_class);

#endif
