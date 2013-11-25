/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <fstream>

#include <util/i2string.h>

#include "qbf_quantor.h"

/*******************************************************************\

Function: qbf_quantort::qbf_quantort

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_quantort::qbf_quantort()
{
}

/*******************************************************************\

Function: qbf_quantort::~qbf_quantort

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_quantort::~qbf_quantort()
{
}

/*******************************************************************\

Function: qbf_quantort::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt qbf_quantort::l_get(literalt a) const
{
  assert(false);
  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: qbf_quantort::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string qbf_quantort::solver_text()
{
  return "Quantor";
}

/*******************************************************************\

Function: qbf_quantort::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt qbf_quantort::prop_solve()
{
  {
    std::string msg=
      "Quantor: "+
      i2string(no_variables())+" variables, "+
      i2string(no_clauses())+" clauses";
    messaget::status(msg);
  }

  std::string qbf_tmp_file="quantor.qdimacs";
  std::string result_tmp_file="quantor.out";

  {
    std::ofstream out(qbf_tmp_file.c_str());

    // write it
    write_qdimacs_cnf(out);
  }
  
  //std::string options=" --equivalences=0";
  std::string options="";

  // solve it
  system(("quantor "+qbf_tmp_file+
         options+
         " -o "+result_tmp_file).c_str());

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

      if(line=="s TRUE")
      {
        result=true;
        result_found=true;
        break;
      }
      else if(line=="s FALSE")
      {
        result=false;
        result_found=true;
        break;
      }
    }

    if(!result_found)
    {
      messaget::error("Quantor failed: unknown result");
      return P_ERROR;
    }    
  }

  if(result)
  {
    messaget::status("Quantor: TRUE");
    return P_SATISFIABLE;
  }
  else
  {
    messaget::status("Quantor: FALSE");
    return P_UNSATISFIABLE;
  }
 
  return P_ERROR;
}

