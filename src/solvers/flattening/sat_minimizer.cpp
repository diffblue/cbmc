/*******************************************************************\

Module:

Author: Georg Weissenbacher, georg.weissenbacher@inf.ethz.ch

\*******************************************************************/

#include <cassert>

#include <i2string.h>
#include <threeval.h>

#include <solvers/sat/satcheck.h>

#include "sat_minimizer.h"

/*******************************************************************\

Function: bv_minimizering_dect::minimize

  Inputs: 

 Outputs:

 Purpose: 

\*******************************************************************/

bool bv_minimizing_dect::minimize(const minimization_listt &symbols)
{
  // unfortunately, only MiniSat supports this

  #if defined(SATCHECK_MINISAT) || defined(SATCHECK_MINISAT2)
  bvt constraints;

  for(minimization_listt::const_iterator
      l_it=symbols.begin();
      l_it!=symbols.end();
      l_it++)
  {
    unsigned result=0;

    const exprt &symbol = *l_it;

    status("Minimizing... ");

    // FIXME: be more gener[ous|al] here!
    assert(symbol.type().id()==ID_unsignedbv);

    unsigned width=boolbv_width(symbol.type());
    
    for(unsigned i = width; i > 0; i--)
    {
      literalt lit;
#if 0
      std::cout << "SYMBOL: " << symbol << std::endl;
#endif
      if(literal(symbol, i-1, lit))
        continue; // there's no corresponding literal
        
      if(lit.is_constant())
        continue;

      literalt nlit=satcheck.lnot(lit);
      constraints.push_back(nlit);

      if(satcheck.l_get(lit)==tvt(false))
        continue;

      // call Minisat with constraints
      satcheck.set_assumptions(constraints);

      if(satcheck.prop_solve() == propt::P_UNSATISFIABLE)
      {
        // change constraint to 1
        constraints.back().swap(lit);
        result |= 1 << (i-1);

        // make sure the model is reconstructed
        satcheck.set_assumptions(constraints);
        if(satcheck.prop_solve()==propt::P_UNSATISFIABLE)
          assert (false); // do not remove call to prop_solve!!
      }
    }

    status(symbol.get_string(ID_identifier)+" = "+i2string(result));
  }

  return true;
  #else
  // we don't have it...
  return false;
  #endif
}


