/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_ID_H
#define CPROVER_CPP_CPP_ID_H

#include <cassert>
#include <list>
#include <map>
#include <string>
#include <set>
#include <iosfwd>

#include <util/expr.h>
#include <util/invariant.h>
#include <util/std_types.h>

class cpp_scopet;

class cpp_idt
{
public:
  cpp_idt();

  enum class id_classt
  {
    UNKNOWN,
    SYMBOL,
    TYPEDEF,
    CLASS,
    ENUM,
    TEMPLATE,
    TEMPLATE_PARAMETER,
    NAMESPACE,
    BLOCK_SCOPE,
    TEMPLATE_SCOPE,
    ROOT_SCOPE,
  };

  bool is_member, is_method, is_static_member,
       is_scope, is_constructor;

  id_classt id_class;

  bool is_class() const
  {
    return id_class==id_classt::CLASS;
  }

  bool is_enum() const
  {
    return id_class==id_classt::ENUM;
  }

  bool is_namespace() const
  {
    return id_class==id_classt::NAMESPACE;
  }

  bool is_typedef() const
  {
    return id_class==id_classt::TYPEDEF;
  }

  bool is_template_scope() const
  {
    return id_class == id_classt::TEMPLATE_SCOPE;
  }

  irep_idt identifier, base_name;

  // if it is a member or method, what class is it in?
  irep_idt class_identifier;
  exprt this_expr;

  // scope data
  std::string prefix, suffix;
  unsigned compound_counter;

  cpp_idt &get_parent() const
  {
    PRECONDITION(parent!=nullptr);
    return *parent;
  }

  void set_parent(cpp_idt &_parent)
  {
    assert(_parent.is_scope);
    parent=&_parent;
  }

  void clear()
  {
    *this=cpp_idt();
  }

  void print(std::ostream &out, unsigned indent=0) const;
  void print_fields(std::ostream &out, unsigned indent=0) const;

protected:
  typedef std::multimap<irep_idt, cpp_idt> cpp_id_mapt;
  cpp_id_mapt sub;

  // These are used for base classes and 'using' clauses.
  typedef std::vector<cpp_idt *> scope_listt;
  scope_listt using_scopes, secondary_scopes;
  cpp_idt *parent;
};

std::ostream &operator<<(std::ostream &out, const cpp_idt &cpp_id);
std::ostream &operator<<(std::ostream &out, const cpp_idt::id_classt &id_class);

#endif // CPROVER_CPP_CPP_ID_H
