
/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/tempfile.h>
#include <util/arith_tools.h>
#include <util/i2string.h>
#include <util/ieee_float.h>

#include "heap_dec.h"

#include "heaptransformer.h"
#include "heapabstraction.h"
#include "heapheuristics.h"
#include "heaprefine.h"


/*******************************************************************\

Function: heap_dect::decision_procedure_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string heap_dect::decision_procedure_text() const
{
  return "hippo";
}


/*******************************************************************\

Function: heap_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt heap_dect::dec_solve()
{
  //call hippo
  heaprefine<heapabs, heaptrans, heapheuristics> solver;
  heapabs sol;
  heapheuristics h;
  heaptrans t(formula);

  transformerRefinementResult::s ret = solver.solve(sol, t, h);

  if(ret==transformerRefinementResult::NotBottom)
  {
    /*    boolean_assignment.clear();
    boolean_assignment.resize(no_boolean_variables, false);

    typedef hash_map_cont<std::string, std::string, string_hash> valuest;
    valuest values;

    while(std::getline(in, line))
    {
      std::size_t pos=line.find(' ');
      if(pos!=std::string::npos)
        values[std::string(line, 0, pos)]=
          std::string(line, pos+1, std::string::npos);
    }

    // Theory variables

    for(identifier_mapt::iterator
        it=identifier_map.begin();
        it!=identifier_map.end();
        it++)
    {
      it->second.value.make_nil();
      std::string conv_id=convert_identifier(it->first);
      std::string value=values[conv_id];
      if(value=="") continue;
      set_value(it->second, value);
    }

    // Booleans

    for(unsigned v=0; v<no_boolean_variables; v++)
    {
      std::string value=values["B"+i2string(v)];
      if(value=="") continue;
      boolean_assignment[v]=(value=="1");
      } */

    return D_SATISFIABLE;
  }
  else if(ret==transformerRefinementResult::Bottom) {
    return D_UNSATISFIABLE;
  }
  assert(false);
}

