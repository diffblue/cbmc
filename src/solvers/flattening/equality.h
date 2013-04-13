/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_FLATTENING_EQUALITY_H
#define CPROVER_SOLVER_FLATTENING_EQUALITY_H

#include <map>

#include <util/hash_cont.h>
#include <util/expr.h>

#include <solvers/prop/prop_conv.h>

class equalityt:public prop_convt
{
public:
  equalityt(
    const namespacet &_ns,
    propt &_prop):prop_convt(_ns, _prop) { }

  virtual literalt equality(const exprt &e1, const exprt &e2);
  
  virtual void post_process()
  {
    add_equality_constraints();
    prop_convt::post_process();
  }

protected:
  typedef hash_map_cont<const exprt, unsigned, irep_hash> elementst;
  typedef std::map<std::pair<unsigned, unsigned>, literalt> equalitiest;
  typedef std::map<unsigned, exprt> elements_revt;

  struct typestructt
  {
    elementst elements;
    elements_revt elements_rev;
    equalitiest equalities;
  };
 
  typedef hash_map_cont<const typet, typestructt, irep_hash> typemapt;
  
  typemapt typemap;    

  virtual literalt equality2(const exprt &e1, const exprt &e2);
  virtual void add_equality_constraints();
  virtual void add_equality_constraints(const typestructt &typestruct);
};

#endif
