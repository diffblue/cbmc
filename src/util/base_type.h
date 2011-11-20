/*******************************************************************\

Module: Base Type Computation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BASE_TYPE_H
#define CPROVER_BASE_TYPE_H

#include <union_find.h>
#include <irep.h>

class exprt;
class typet;
class namespacet;

// these go away
void __old_base_type(typet &type, const namespacet &ns);
void __old_base_type(exprt &expr, const namespacet &ns);

bool base_type_eq(
  const typet &type1,
  const typet &type2,
  const namespacet &ns);

bool base_type_eq(
  const exprt &expr1,
  const exprt &expr2,
  const namespacet &ns);

/*******************************************************************\

   Class: base_type_eqt

 Purpose:

\*******************************************************************/

class base_type_eqt
{
public:
  base_type_eqt(const namespacet &_ns):ns(_ns)
  {
  }

  bool base_type_eq(const typet &type1, const typet &type2)
  {
    identifiers.clear();
    return base_type_eq_rec(type1, type2);
  }
  
  bool base_type_eq(const exprt &expr1, const exprt &expr2)
  {
    identifiers.clear();
    return base_type_eq_rec(expr1, expr2);
  }
  
  virtual ~base_type_eqt() { }

protected:
  const namespacet &ns;

  virtual bool base_type_eq_rec(const typet &type1, const typet &type2);
  virtual bool base_type_eq_rec(const exprt &expr1, const exprt &expr2);
  
  // for loop avoidance
  typedef union_find<irep_idt> identifierst;
  identifierst identifiers;
};

#endif
