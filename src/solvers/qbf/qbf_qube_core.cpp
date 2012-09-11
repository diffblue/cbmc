/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>

#include <fstream>

#include <util/i2string.h>
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
    std::string msg=
      "QuBE: "+
      i2string(no_variables())+" variables, "+
      i2string(no_clauses())+" clauses";
    messaget::status(msg);
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
  system(("QuBE " + options + " " + qbf_tmp_file +
          " > "+result_tmp_file).c_str());

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
          assignment[b.negate().to_ulong()] = false;
        else
          assignment[b.to_ulong()] = true;
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
      messaget::error("QuBE failed: unknown result");
      return P_ERROR;
    }
  }

  remove(result_tmp_file.c_str());
  remove(qbf_tmp_file.c_str());

  if(result)
  {
    messaget::status("QuBE: TRUE");
    return P_SATISFIABLE;
  }
  else
  {
    messaget::status("QuBE: FALSE");
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
