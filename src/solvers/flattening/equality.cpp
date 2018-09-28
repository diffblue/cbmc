/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "equality.h"

#ifdef DEBUG
#include <iostream>
#endif

#include "bv_utils.h"

literalt equalityt::equality(const exprt &e1, const exprt &e2)
{
  if(e1<e2)
    return equality2(e1, e2);
  else
    return equality2(e2, e1);
}

literalt equalityt::equality2(const exprt &e1, const exprt &e2)
{
  PRECONDITION(e1.type() == e2.type());

  const typet &type = e1.type();

  // check for syntactical equality

  if(e1==e2)
    return const_literal(true);

  // check for boolean equality

  INVARIANT(
    type.id() != ID_bool, "method shall not be used to compare Boolean types");

  // look it up

  typestructt &typestruct=typemap[type];
  elementst &elements=typestruct.elements;
  elements_revt &elements_rev=typestruct.elements_rev;
  equalitiest &equalities=typestruct.equalities;

  std::pair<unsigned, unsigned> u;

  {
    std::pair<elementst::iterator, bool> result=
      elements.insert(std::pair<exprt, unsigned>(e1, elements.size()));

    u.first=result.first->second;

    if(result.second)
      elements_rev[u.first]=e1;
  }

  {
    std::pair<elementst::iterator, bool> result=
      elements.insert(elementst::value_type(e2, elements.size()));

    u.second=result.first->second;

    if(result.second)
      elements_rev[u.second]=e2;
  }

  literalt l;

  {
    equalitiest::const_iterator result=equalities.find(u);

    if(result==equalities.end())
    {
      l=prop.new_variable();
      if(freeze_all && !l.is_constant())
        prop.set_frozen(l);
      equalities.insert(equalitiest::value_type(u, l));
    }
    else
      l=result->second;
  }

  return l;
}

void equalityt::add_equality_constraints()
{
  for(typemapt::const_iterator it=typemap.begin();
      it!=typemap.end(); it++)
    add_equality_constraints(it->second);
}

void equalityt::add_equality_constraints(const typestructt &typestruct)
{
  std::size_t no_elements=typestruct.elements.size();
  std::size_t bits=0;

  // get number of necessary bits

  for(std::size_t i=no_elements; i!=0; bits++)
    i=(i>>1);

  // generate bit vectors

  std::vector<bvt> eq_bvs;

  eq_bvs.resize(no_elements);

  for(std::size_t i=0; i<no_elements; i++)
  {
    eq_bvs[i].resize(bits);
    for(std::size_t j=0; j<bits; j++)
      eq_bvs[i][j]=prop.new_variable();
  }

  // generate equality constraints

  bv_utilst bv_utils(prop);

  for(equalitiest::const_iterator
      it=typestruct.equalities.begin();
      it!=typestruct.equalities.end();
      it++)
  {
    const bvt &bv1=eq_bvs[it->first.first];
    const bvt &bv2=eq_bvs[it->first.second];

    prop.set_equal(bv_utils.equal(bv1, bv2), it->second);
  }
}
