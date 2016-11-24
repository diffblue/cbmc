/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <fstream>

#include "qbf_qube.h"

/*******************************************************************\

Function: qbf_qubet::qbf_qubet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_qubet::qbf_qubet()
{
  // skizzo crashes on broken lines
  break_lines=false;
}

/*******************************************************************\

Function: qbf_qubet::~qbf_qubet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_qubet::~qbf_qubet()
{
}

/*******************************************************************\

Function: qbf_qubet::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt qbf_qubet::l_get(literalt a) const
{
  assert(false);
  return tvt(false);
}

/*******************************************************************\

Function: qbf_qubet::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string qbf_qubet::solver_text()
{
  return "QuBE";
}

/*******************************************************************\

Function: qbf_qubet::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt qbf_qubet::prop_solve()
{
  // sKizzo crashes on empty instances
  if(no_clauses()==0)
    return P_SATISFIABLE;

  {
    messaget::status() << 
      "QuBE: " <<
      no_variables() << " variables, " <<
      no_clauses() << " clauses" << eom;
  }

  std::string qbf_tmp_file="qube.qdimacs";
  std::string result_tmp_file="qube.out";

  {
    std::ofstream out(qbf_tmp_file.c_str());

    // write it
    write_qdimacs_cnf(out);
  }

  //std::string options=" --equivalences=0";
  std::string options="";

  // solve it
  int res=system(("QuBE "+qbf_tmp_file+
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

      if(line=="s cnf 0")
      {
        result=true;
        result_found=true;
        break;
      }
      else if(line=="s cnf 1")
      {
        result=false;
        result_found=true;
        break;
      }
    }

    if(!result_found)
    {
      messaget::error() << "QuBE failed: unknown result" << eom;
      return P_ERROR;
    }
  }

  if(result)
  {
    messaget::status() << "QuBE: TRUE" << eom;
    return P_SATISFIABLE;
  }
  else
  {
    messaget::status() << "QuBE: FALSE" << eom;
    return P_UNSATISFIABLE;
  }

  return P_ERROR;
}

