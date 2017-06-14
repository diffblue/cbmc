/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <cassert>
#include <cstdlib>
#include <fstream>

#include "qbf_quantor.h"

qbf_quantort::qbf_quantort()
{
}

qbf_quantort::~qbf_quantort()
{
}

tvt qbf_quantort::l_get(literalt a) const
{
  assert(false);
  return tvt::unknown();
}

const std::string qbf_quantort::solver_text()
{
  return "Quantor";
}

propt::resultt qbf_quantort::prop_solve()
{
  {
    messaget::status() <<
      "Quantor: " <<
      no_variables() << " variables, " <<
      no_clauses() << " clauses" << eom;
  }

  std::string qbf_tmp_file="quantor.qdimacs";
  std::string result_tmp_file="quantor.out";

  {
    std::ofstream out(qbf_tmp_file.c_str());

    // write it
    write_qdimacs_cnf(out);
  }

  // solve it
  int res=system((
    "quantor "+qbf_tmp_file+" -o "+result_tmp_file).c_str());
  assert(0==res);

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
      messaget::error() << "Quantor failed: unknown result" << eom;
      return resultt::P_ERROR;
    }
  }

  if(result)
  {
    messaget::status() << "Quantor: TRUE" << eom;
    return resultt::P_SATISFIABLE;
  }
  else
  {
    messaget::status() << "Quantor: FALSE" << eom;
    return resultt::P_UNSATISFIABLE;
  }

  return resultt::P_ERROR;
}
