/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <fstream>

#include <util/i2string.h>
#include <util/string2int.h>

#include "satcheck_zcore.h"

#include <cstring>

/*******************************************************************\

Function: satcheck_zcoret::satcheck_zcoret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_zcoret::satcheck_zcoret()
{
}

/*******************************************************************\

Function: satcheck_zcoret::~satcheck_zcoret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_zcoret::~satcheck_zcoret()
{
}

/*******************************************************************\

Function: satcheck_zcoret::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_zcoret::l_get(literalt a) const
{
  assert(false);
  return tvt(tvt::tv_enumt::TV_UNKNOWN);
}

/*******************************************************************\

Function: satcheck_zcoret::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_zcoret::solver_text()
{
  return "ZCore";
}

/*******************************************************************\

Function: satcheck_zcoret::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_zcoret::prop_solve()
{
  // We start counting at 1, thus there is one variable fewer.
  {
    std::string msg=
      i2string(no_variables()-1)+" variables, "+
      i2string(no_clauses())+" clauses";
    messaget::status() << msg << messaget::eom;
  }

  // get the core
  std::string cnf_file="cnf.dimacs";
  std::string core_file="unsat_core.cnf";
  std::string trace_file="resolve_trace";
  std::string output_file="cnf.out";

  {
    std::ofstream out(cnf_file.c_str(), std::ios::out);
    write_dimacs_cnf(out);
  }
  
  // generate resolve_trace
  system(std::string("zchaff_verify "+cnf_file+" > "+output_file).c_str());

  // get core
  system(std::string("zcore "+cnf_file+" "+trace_file+" >> "+output_file).c_str());

  in_core.clear();

  // read result
  {
    std::ifstream in(core_file.c_str());
    
    while(true)
    {
      std::string line;
      if(!std::getline(in, line)) break;
      
      if(!(line.substr(0,1)=="c" || line.substr(0,1)=="p"))
      {
        const char *p=line.c_str();
        
        while(true)
        {
          int l=unsafe_str2int(p);
          if(l==0) break;
          
          if(l<0) l=-l;

          in_core.insert(l);
          
          // next one
          const char *q=strchr(p, ' ');
          while(*q==' ') q++;
          if(q==NULL) break;
          p=q;
        }
      }
    }
  }
  
  if(in_core.empty())
    return P_ERROR;
  
  remove(cnf_file.c_str());
  //remove(core_file.c_str());
  remove(trace_file.c_str());
  //remove(output_file.c_str());

  return P_UNSATISFIABLE;
}
