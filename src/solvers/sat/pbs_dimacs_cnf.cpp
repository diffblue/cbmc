/*******************************************************************\

Module:

Author: Alex Groce

\*******************************************************************/

#include "pbs_dimacs_cnf.h"

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>

void pbs_dimacs_cnft::write_dimacs_pb(std::ostream &out)
{
  double d_sum=0;

  // std::cout << "enter: No Lit.=" << no_variables () << "\n";

  for(std::map<literalt, unsigned>::const_iterator it=pb_constraintmap.begin();
      it!=pb_constraintmap.end(); ++it)
    d_sum += ((*it).second);

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
    int dimacs_lit=lit_entry.first.dimacs();
    out << "v" << dimacs_lit << " c" << lit_entry.second << "\n";
  }

  // std::cout << "exit: No Lit.=" << no_variables () << "\n";
}

bool pbs_dimacs_cnft::pbs_solve()
{
  // std::cout << "solve: No Lit.=" << no_variables () << "\n";

  std::string command;

  if(!pbs_path.empty())
  {
    command += pbs_path;
    if(command.substr(command.length(), 1)!="/")
      command += "/";
  }

  command += "pbs";

  // std::cout << "PBS COMMAND IS: " << command << "\n";
  /*
    if (!(getenv("PBS_PATH")==NULL))
    {
    command=getenv("PBS_PATH");
    }
    else
    {
    error ("Unable to read PBS_PATH environment variable.\n");
    return false;
    }
  */

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
      // std::cout << "NO BINARY SEARCH" << "\n";
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

  int res=system(command.c_str());
  assert(0==res);

  std::ifstream file("temp.out");
  std::string line;
  int v;
  bool satisfied=false;

  if(file.fail())
  {
    error() << "Unable to read SAT results!" << eom;
    return false;
  }

  opt_sum=-1;

  while(file && !file.eof ())
    {
      std::getline(file, line);
      if(strstr(line.c_str(),
                "Variable Assignments Satisfying CNF Formula:")!=nullptr)
        {
          // print ("Reading assignments...\n");
          // std::cout << "No literals: " << no_variables() << "\n";
          satisfied=true;
          assigned.clear();
          for(size_t i=0; (file && (i < no_variables())); ++i)
            {
              file >> v;
              if(v > 0)
                {
                  // std::cout << v << " ";
                  assigned.insert(v);
                }
            }
          // std::cout << "\n";
          // print ("Finished reading assignments.\n");
        }
      else if(strstr(line.c_str(), "SAT... SUM")!=nullptr)
        {
          // print (line);
          sscanf(line.c_str(), "%*s %*s %*s %d", &opt_sum);
        }
      else if(strstr(line.c_str(), "SAT - All implied")!=nullptr)
        {
          // print (line);
          sscanf(
            line.c_str(),
            "%*s %*s %*s %*s %*s %*s %*s %*s %*s %*s %*s %d",
            &opt_sum);
        }
      else if(strstr(line.c_str(), "SAT... Solution")!=nullptr)
        {
          // print(line);
          sscanf(line.c_str(), "%*s %*s %*s %d", &opt_sum);
        }
      else if(strstr(line.c_str(), "Optimal Soln")!=nullptr)
        {
          // print(line);
          if(strstr(line.c_str(), "time out")!=nullptr)
            {
              status() << "WARNING:  TIMED OUT.  SOLUTION MAY BE INCORRECT."
                       << eom;
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
  messaget::status() <<
    (no_variables()-1) << " variables, " <<
    clauses.size() << " clauses" << eom;

  bool result=pbs_solve();

  if(!result)
  {
    messaget::status() <<
      "PBS checker: system is UNSATISFIABLE" << eom;
  }
  else
  {
    messaget::status() <<
      "PBS checker: system is SATISFIABLE";
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
  int dimacs_lit=a.dimacs();

  // std::cout << a << " / " << dimacs_lit << "=";

  bool neg=(dimacs_lit < 0);
  if(neg)
    dimacs_lit=-dimacs_lit;

  std::set<int>::const_iterator f=assigned.find(dimacs_lit);

  if(!neg)
    {
      if(f==assigned.end())
        {
          // std::cout << "FALSE" << "\n";
          return tvt(false);
        }
      else
        {
          // std::cout << "TRUE" << "\n";
          return tvt(true);
        }
    }
  else
    {
      if(f!=assigned.end())
        {
          // std::cout << "FALSE" << "\n";
          return tvt(false);
        }
      else
        {
          // std::cout << "TRUE" << "\n";
          return tvt(true);
        }
    }
}
