/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "icnf.h"

template <class sub_solvert>
void icnft<sub_solvert>::lcnf(const bvt &bv)
{
  // add clause to sub-solver
  sub_solvert::lcnf(bv);

  // clause trivially satisfied?
  for(const auto l : bv)
    if(l.is_true())
      return;

  // write the clause
  for(const auto l : bv)
  {
    if(!l.is_false())
      out << l.dimacs() << ' ';
  }

  out << "0\n";
}

template <class sub_solvert>
propt::resultt icnft<sub_solvert>::do_prop_solve()
{
  // write the assumptions, unless we assume 'false'
  if(
    std::find(assumptions.begin(), assumptions.end(), const_literal(false)) ==
    assumptions.end())
  {
    out << "a ";
    for(const auto l : assumptions)
    {
      if(!l.is_true())
        out << l.dimacs() << ' ';
    }

    out << "0\n";
  }

  return sub_solvert::do_prop_solve();
}

// instances
template class icnft<satcheck_minisat_simplifiert>;
template class icnft<satcheck_minisat_no_simplifiert>;
