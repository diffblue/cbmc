/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <fstream>

#include <util/mp_arith.h>

#include "qbf_qube_core.h"

/*******************************************************************\

Function: qbf_qube_coret::qbf_qube_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_qube_coret::qbf_qube_coret() : qdimacs_coret()
{
  break_lines=false;
  qbf_tmp_file="qube.qdimacs";
}

/*******************************************************************\

Function: qbf_qube_coret::~qbf_qube_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_qube_coret::~qbf_qube_coret()
{
}

/*******************************************************************\

Function: qbf_qube_coret::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string qbf_qube_coret::solver_text()
{
  return "QuBE w/ toplevel assignments";
}

/*******************************************************************\

Function: qbf_qube_coret::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt qbf_qube_coret::prop_solve()
{
  if(no_clauses()==0)
    return P_SATISFIABLE;

  {
    messaget::status() << 
      "QuBE: " <<
      no_variables() << " variables, " <<
      no_clauses() << " clauses" << eom;
  }

  std::string result_tmp_file="qube.out";

  {
    std::ofstream out(qbf_tmp_file.c_str());

    // write it
    break_lines=false;
    write_qdimacs_cnf(out);
  }

  std::string options="";

  // solve it
  int res=system(("QuBE " + options + " " + qbf_tmp_file +
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

      if(line[0]=='V')
      {
        mp_integer b(line.substr(2).c_str());
        if(b<0)
          assignment[integer2unsigned(b.negate())] = false;
        else
          assignment[integer2unsigned(b)] = true;
      }
      else if(line=="s cnf 1")
      {
        result=true;
        result_found=true;
        break;
      }
      else if(line=="s cnf 0")
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

  remove(result_tmp_file.c_str());
  remove(qbf_tmp_file.c_str());

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
}

/*******************************************************************\

Function: qbf_qube_coret::is_in_core

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool qbf_qube_coret::is_in_core(literalt l) const
{
  throw ("Not supported");
}

/*******************************************************************\

Function: qbf_qube_coret::m_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qdimacs_coret::modeltypet qbf_qube_coret::m_get(literalt a) const
{
  throw ("not supported");
}
