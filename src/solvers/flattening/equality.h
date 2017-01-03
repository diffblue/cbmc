/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_FLATTENING_EQUALITY_H
#define CPROVER_SOLVERS_FLATTENING_EQUALITY_H

#include <map>

#include <util/expr.h>

#include <solvers/prop/prop_conv.h>

class equalityt:public prop_conv_solvert
{
public:
  equalityt(
    const namespacet &_ns,
    propt &_prop):prop_conv_solvert(_ns, _prop) { }

  virtual literalt equality(const exprt &e1, const exprt &e2);

  void post_process() override
  {
    add_equality_constraints();
    prop_conv_solvert::post_process();
    typemap.clear(); // if called incrementally, don't do it twice
  }

protected:
  typedef std::unordered_map<const exprt, unsigned, irep_hash> elementst;
  typedef std::map<std::pair<unsigned, unsigned>, literalt> equalitiest;
  typedef std::map<unsigned, exprt> elements_revt;

  struct typestructt
  {
    elementst elements;
    elements_revt elements_rev;
    equalitiest equalities;
  };

  typedef std::unordered_map<const typet, typestructt, irep_hash> typemapt;

  typemapt typemap;

  virtual literalt equality2(const exprt &e1, const exprt &e2);
  virtual void add_equality_constraints();
  virtual void add_equality_constraints(const typestructt &typestruct);
};

#endif // CPROVER_SOLVERS_FLATTENING_EQUALITY_H
