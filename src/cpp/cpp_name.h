/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_CPP_CPP_NAME_H
#define CPROVER_CPP_CPP_NAME_H

#include <util/expr.h>
#include <util/invariant.h>

class cpp_namet:public irept
{
public:
  // the subs are one of the following:
  // ID_name (see namet)
  // ID_operator
  // ID_template_args
  // ::
  // ~

  class namet:public irept
  {
  public:
    namet():irept(ID_name)
    {
    }

    explicit namet(const irep_idt &base_name):irept(ID_name)
    {
      set(ID_identifier, base_name);
    }

    namet(
      const irep_idt &_base_name,
      const source_locationt &_source_location):irept(ID_name)
    {
      set(ID_identifier, _base_name);
      add_source_location()=_source_location;
    }

    source_locationt &add_source_location()
    {
      return static_cast<source_locationt &>(add(ID_C_source_location));
    }

    const source_locationt &source_location() const
    {
      return static_cast<const source_locationt &>(find(ID_C_source_location));
    }
  };

  cpp_namet():irept(ID_cpp_name)
  {
  }

  explicit cpp_namet(const irep_idt &base_name):irept(ID_cpp_name)
  {
    get_sub().push_back(namet(base_name));
  }

  cpp_namet(
    const irep_idt &_base_name,
    const source_locationt &_source_location):irept(ID_cpp_name)
  {
    get_sub().push_back(namet(_base_name, _source_location));
  }

  const source_locationt &source_location() const
  {
    if(get_sub().empty())
      return source_locationt::nil();
    else
      return static_cast<const source_locationt &>(
        get_sub().front().find(ID_C_source_location));
  }

  // void convert(std::string &identifier, std::string &base_name) const;
  irep_idt get_base_name() const;

  // one of three:
  // 'identifier'
  // 'operator X'
  // '~identifier'
  bool is_simple_name() const
  {
    const subt &sub=get_sub();
    return (sub.size()==1 && sub.front().id()==ID_name) ||
           (sub.size()==2 && sub.front().id()==ID_operator) ||
           (sub.size()==2 && sub[0].id()=="~" && sub[1].id()==ID_name);
  }

  bool is_operator() const
  {
    if(get_sub().empty())
      return false;
    return get_sub().front().id()==ID_operator;
  }

  bool is_typename() const
  {
    return get_bool(ID_typename);
  }

  bool is_qualified() const
  {
    for(const auto &irep : get_sub())
    {
      if(irep.id() == "::")
        return true;
    }
    return false;
  }

  bool is_destructor() const
  {
    return get_sub().size()>=1 && get_sub().front().id()=="~";
  }

  bool has_template_args() const
  {
    for(const auto &irep : get_sub())
    {
      if(irep.id() == ID_template_args)
        return true;
    }

    return false;
  }

  std::string to_string() const;

  const exprt &as_expr() const
  {
    return static_cast<const exprt &>(static_cast<const irept &>(*this));
  }

  const typet &as_type() const
  {
    return static_cast<const typet &>(static_cast<const irept &>(*this));
  }
};

inline cpp_namet &to_cpp_name(irept &cpp_name)
{
  PRECONDITION(cpp_name.id() == ID_cpp_name);
  return static_cast<cpp_namet &>(cpp_name);
}

inline const cpp_namet &to_cpp_name(const irept &cpp_name)
{
  PRECONDITION(cpp_name.id() == ID_cpp_name);
  return static_cast<const cpp_namet &>(cpp_name);
}

#endif // CPROVER_CPP_CPP_NAME_H
