/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

// THIS FILE IS DEPRECATED

#ifndef CPROVER_NAMESPACE_UTILS_H
#define CPROVER_NAMESPACE_UTILS_H

#include <functional>
#include "namespace.h"
#include "base_type.h"
#include "type_eq.h"
#include "std_expr.h"

// second: true <=> not found

class namespace_utils_baset
{
 public:
  virtual ~namespace_utils_baset()
  {
  }
 
  const symbolt &lookup(const irep_idt &name) const
  {
    const symbolt *symbol;
    if(lookup(name, symbol))
      throw "identifier "+id2string(name)+" not found";
    return *symbol;
  }
   
  const symbolt &lookup(const symbol_exprt &symbol_expr) const
  {
    const symbolt *symbol;
    if(lookup(symbol_expr.get_identifier(), symbol))
      throw "identifier "+id2string(symbol_expr.get_identifier())+" not found";
    return *symbol;
  }
   
  bool lookup(const irep_idt &name, const symbolt *&symbol) const
  {
    return ns().lookup(name, symbol);
  }

  bool lookup_symbol(const exprt &symbol_expr, const symbolt *&symbol) const
  {
    return ns().lookup(symbol_expr.get(ID_identifier), symbol);
  }

  void follow_symbol(irept &irep) const
  {
    ns().follow_symbol(irep);
  }

  void follow_macros(exprt &expr) const
  {
    ns().follow_macros(expr);
  }

  /*
  void base_type(typet &type)
  {
    ::base_type(type, ns());
  }
   
  void base_type(exprt &expr)
  {
    ::base_type(expr, ns());
  }
  */


private:
  bool does_symbol_match(
    const exprt& lvalue,
    std::function<bool(symbolt)> predicate) const;

public:
  bool is_parameter(const exprt& lvalue) const;
  bool is_static(const exprt& lvalue) const;
  bool is_auxiliary_variable(const exprt& lvalue) const;
  bool is_return_value_auxiliary(const exprt& lvalue) const;

  bool type_eq(const typet &type1, const typet &type2)
  {
    return ::type_eq(type1, type2, ns());
  }

  bool base_type_eq(const typet &type1, const typet &type2)
  {
    return ::base_type_eq(type1, type2, ns());
  }

 protected:
  virtual const namespacet &ns() const=0;
};
 
class namespace_utilst:public virtual namespace_utils_baset
{
 public:
  namespace_utilst(const namespacet &_ns):__ns(_ns){}
  
 protected:
  const namespacet &__ns;

  virtual const namespacet &ns() const
  {
    return __ns;
  }
};
 
#endif
