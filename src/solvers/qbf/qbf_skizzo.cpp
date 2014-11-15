/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <fstream>

#include "qbf_skizzo.h"

/*******************************************************************\

Function: qbf_skizzot::qbf_skizzot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_skizzot::qbf_skizzot()
{
  // skizzo crashes on broken lines
  break_lines=false;
}

/*******************************************************************\

Function: qbf_skizzot::~qbf_skizzot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_skizzot::~qbf_skizzot()
{
}

/*******************************************************************\

Function: qbf_skizzot::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt qbf_skizzot::l_get(literalt a) const
{
  assert(false);
  return tvt(false);
}

/*******************************************************************\

Function: qbf_skizzot::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string qbf_skizzot::solver_text()
{
  return "Skizzo";
}

/*******************************************************************\

Function: qbf_skizzot::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt qbf_skizzot::prop_solve()
{
  // sKizzo crashes on empty instances
  if(no_clauses()==0)
    return P_SATISFIABLE;
  
  {
    messaget::status() <<
      "Skizzo: " <<
      no_variables() << " variables, " <<
      no_clauses() << " clauses" << eom;
  }

  std::string qbf_tmp_file="sKizzo.qdimacs";
  std::string result_tmp_file="sKizzo.out";

  {
    std::ofstream out(qbf_tmp_file.c_str());

    // write it
    write_qdimacs_cnf(out);
  }
  
  //std::string options=" --equivalences=0";
  std::string options="";

  // solve it
  int res=system(("sKizzo "+qbf_tmp_file+
         options+
         " > "+result_tmp_file).c_str());
  assert(0 == res);

  bool result=false;
  
  // read result
  {
    std::ifstream in(result_tmp_file.c_str());
    
    bool result_found=false;
    while(in)
    {
      std::string line;

      std::getline(in, line);
      
      if(line!="" && line[line.size()-1]=='\r')
        line.resize(line.size()-1);

      if(line=="The instance evaluates to TRUE.")
      {
        result=true;
        result_found=true;
        break;
      }
      else if(line=="The instance evaluates to FALSE.")
      {
        result=false;
        result_found=true;
        break;
      }
    }

    if(!result_found)
    {
      messaget::error() << "Skizzo failed: unknown result" << eom;
      return P_ERROR;
    }    
  }

  if(result)
  {
    messaget::status() << "Skizzo: TRUE" << eom;
    return P_SATISFIABLE;
  }
  else
  {
    messaget::status() << "Skizzo: FALSE" << eom;
    return P_UNSATISFIABLE;
  }
 
  return P_ERROR;
}

