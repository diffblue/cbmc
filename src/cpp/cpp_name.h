/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_CPP_NAME_H
#define CPROVER_CPP_CPP_NAME_H

#include "location.h"

class cpp_namet:public irept
{
public:
  cpp_namet():irept(ID_cpp_name)
  {
  }

  const locationt &location() const
  {
    if(get_sub().empty())
      return static_cast<const locationt &>(get_nil_irep());
    else
      return static_cast<const locationt &>(get_sub().front().find(ID_C_location));
  }

  //void convert(std::string &identifier, std::string &base_name) const;
  irep_idt get_base_name() const;
  
  // one of three:
  // 'string'
  // 'operator X'
  // '~string'
  inline bool is_simple_name() const
  {
    const subt &sub=get_sub();
    return (sub.size()==1 && sub.front().id()==ID_name) ||
           (sub.size()==2 && sub.front().id()==ID_operator) ||
           (sub.size()==2 && sub[0].id()=="~" && sub[1].id()==ID_name);
  }

  bool is_operator() const
  {
    if(get_sub().empty()) return false;
    return get_sub().front().id()==ID_operator;
  }

  bool is_typename() const
  {
    return get_bool(ID_typename);
  }

  bool is_qualified() const
  {
    forall_irep(it, get_sub())
      if(it->id()=="::")
        return true;
    return false;
  }
  
  bool is_destructor() const
  {
    return get_sub().size()>=1 && get_sub().front().id()=="~";
  }

  bool has_template_args() const
  {
    forall_irep(it, get_sub())
      if(it->id()==ID_template_args)
        return true;

    return false;
  }

  std::string to_string() const;
};

inline cpp_namet &to_cpp_name(irept &cpp_name)
{
  assert(cpp_name.id() == ID_cpp_name);
  return static_cast<cpp_namet &>(cpp_name);
}

inline const cpp_namet &to_cpp_name(const irept &cpp_name)
{
  assert(cpp_name.id() == ID_cpp_name);
  return static_cast<const cpp_namet &>(cpp_name);
}

#endif
