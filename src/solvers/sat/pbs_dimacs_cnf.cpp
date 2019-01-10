/*******************************************************************\

Module:

Author: Alex Groce

\*******************************************************************/

#include "pbs_dimacs_cnf.h"

#include <cstdlib>
#include <cstring>
#include <fstream>

#ifdef DEBUG
#include <iostream>
#endif

void pbs_dimacs_cnft::write_dimacs_pb(std::ostream &out)
{
  double d_sum = 0;

#ifdef DEBUG
  std::cout << "enter: No Lit.=" << no_variables() << "\n";
#endif

  for(const auto &lit_entry : pb_constraintmap)
    d_sum += lit_entry.second;

  if(!optimize)
  {
    out << "# PBType: E" << "\n";
    out << "# PBGoal: " << goal << "\n";
  }
  else if(!maximize)
  {
    out << "# PBType: SE" << "\n";
    out << "# PBGoal: " << d_sum << "\n";
    out << "# PBObj : MIN" << "\n";
  }
  else
  {
    out << "# PBType: GE" << "\n";
    out << "# PBGoal: " << 0 << "\n";
    out << "# PBObj : MAX" << "\n";
  }

  out << "# NumCoef: " << pb_constraintmap.size() << "\n";

  for(const auto &lit_entry : pb_constraintmap)
  {
    const int dimacs_lit = lit_entry.first.dimacs();
    out << "v" << dimacs_lit << " c" << lit_entry.second << "\n";
  }

#ifdef DEBUG
  std::cout << "exit: No Lit.=" << no_variables() << "\n";
#endif
}

bool pbs_dimacs_cnft::pbs_solve()
{
#ifdef DEBUG
  std::cout << "solve: No Lit.=" << no_variables() << "\n";
#endif

  std::string command;

  if(!pbs_path.empty())
  {
    command += pbs_path;
    if(command.substr(command.length(), 1) != "/")
      command += "/";
  }

  command += "pbs";

#ifdef DEBUG
  std::cout << "PBS COMMAND IS: " << command << "\n";
#endif
#if 0
  if (!(getenv("PBS_PATH")==NULL))
  {
    command=getenv("PBS_PATH");
  }
  else
  {
    error ("Unable to read PBS_PATH environment variable.\n");
    return false;
  }
#endif

  command += " -f temp.cnf";

#if 1
  if(optimize)
  {
    if(binary_search)
    {
      command += " -S 1000 -D 1 -H -I -a";
    }
    else
    {
#ifdef DEBUG
      std::cout << "NO BINARY SEARCH"
                << "\n";
#endif
      command += " -S 1000 -D 1 -I -a";
    }
  }
  else
  {
    command += " -S 1000 -D 1 -a";
  }
#else
  command += " -z";
#endif

  command += " -a > temp.out";

  const int res = system(command.c_str());
  CHECK_RETURN(0 == res);

  std::ifstream file("temp.out");
  std::string line;
  int v;
  bool satisfied = false;

  if(file.fail())
  {
    error() << "Unable to read SAT results!" << eom;
    return false;
  }

  opt_sum = -1;

  while(file && !file.eof())
  {
    std::getline(file, line);
    if(
      strstr(line.c_str(), "Variable Assignments Satisfying CNF Formula:") !=
      nullptr)
    {
#ifdef DEBUG
      std::cout << "Reading assignments...\n";
      std::cout << "No literals: " << no_variables() << "\n";
#endif
      satisfied = true;
      assigned.clear();
      for(size_t i = 0; (file && (i < no_variables())); ++i)
      {
        file >> v;
        if(v > 0)
        {
#ifdef DEBUG
          std::cout << v << " ";
#endif
          assigned.insert(v);
        }
      }
#ifdef DEBUG
      std::cout << "\n";
      std::cout << "Finished reading assignments.\n";
#endif
    }
    else if(strstr(line.c_str(), "SAT... SUM") != nullptr)
    {
#ifdef DEBUG
      std::cout << line;
#endif
      sscanf(line.c_str(), "%*s %*s %*s %d", &opt_sum);
    }
    else if(strstr(line.c_str(), "SAT - All implied") != nullptr)
    {
#ifdef DEBUG
      std::cout << line;
#endif
      sscanf(
        line.c_str(),
        "%*s %*s %*s %*s %*s %*s %*s %*s %*s %*s %*s %d",
        &opt_sum);
    }
    else if(strstr(line.c_str(), "SAT... Solution") != nullptr)
    {
#ifdef DEBUG
      std::cout << line;
#endif
      sscanf(line.c_str(), "%*s %*s %*s %d", &opt_sum);
    }
    else if(strstr(line.c_str(), "Optimal Soln") != nullptr)
    {
#ifdef DEBUG
      std::cout << line;
#endif
      if(strstr(line.c_str(), "time out") != nullptr)
      {
        status() << "WARNING:  TIMED OUT.  SOLUTION MAY BE INCORRECT." << eom;
        return satisfied;
      }
      sscanf(line.c_str(), "%*s %*s %*s %d", &opt_sum);
    }
  }

  return satisfied;
}

propt::resultt pbs_dimacs_cnft::prop_solve()
{
  std::ofstream file("temp.cnf");

  write_dimacs_cnf(file);

  std::ofstream pbfile("temp.cnf.pb");

  write_dimacs_pb(pbfile);

  file.close();
  pbfile.close();

  // We start counting at 1, thus there is one variable fewer.
  messaget::statistics() << (no_variables() - 1) << " variables, "
                         << clauses.size() << " clauses" << eom;

  const bool result = pbs_solve();

  if(!result)
  {
    messaget::status() << "PBS checker: system is UNSATISFIABLE" << eom;
  }
  else
  {
    messaget::status() << "PBS checker: system is SATISFIABLE";
    if(optimize)
      messaget::status() << " (distance " << opt_sum << ")";
    messaget::status() << eom;
  }

  if(result)
    return resultt::P_SATISFIABLE;
  else
    return resultt::P_UNSATISFIABLE;
}

tvt pbs_dimacs_cnft::l_get(literalt a) const
{
  int dimacs_lit = a.dimacs();

#ifdef DEBUG
  std::cout << a << " / " << dimacs_lit << "=";
#endif

  const bool neg = (dimacs_lit < 0);
  if(neg)
    dimacs_lit = -dimacs_lit;

  std::set<int>::const_iterator f = assigned.find(dimacs_lit);

  if(!neg)
  {
    if(f == assigned.end())
    {
#ifdef DEBUG
      std::cout << "FALSE\n";
#endif
      return tvt(false);
    }
    else
    {
#ifdef DEBUG
      std::cout << "TRUE\n";
#endif
      return tvt(true);
    }
  }
  else
  {
    if(f != assigned.end())
    {
#ifdef DEBUG
      std::cout << "FALSE\n";
#endif
      return tvt(false);
    }
    else
    {
#ifdef DEBUG
      std::cout << "TRUE\n";
#endif
      return tvt(true);
    }
  }
}
