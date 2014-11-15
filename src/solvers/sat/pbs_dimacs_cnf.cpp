/*******************************************************************\

Module:

Author: Alex Groce

\*******************************************************************/

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>

#include "pbs_dimacs_cnf.h"

/*******************************************************************\

Function: pbs_dimacs_cnft::write_dimacs_cnf_pb

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pbs_dimacs_cnft::write_dimacs_pb(std::ostream &out)
{
  double d_sum = 0;

  //std::cout << "enter: No Lit. = " << no_variables () << "\n";

  for(std::map<literalt,unsigned>::const_iterator it=pb_constraintmap.begin();
      it != pb_constraintmap.end (); ++it)
    d_sum += ((*it).second);

  if (!optimize)
  {
    out << "# PBType: E" << "\n";
    out << "# PBGoal: " << goal << "\n";
  }
  else if (!maximize)
  {
    out << "# PBType: SE" << "\n";
    out << "# PBGoal: " << d_sum << "\n";
    out << "# PBObj : MIN" << "\n";
  } else
  {
    out << "# PBType: GE" << "\n";
    out << "# PBGoal: " << 0 << "\n";
    out << "# PBObj : MAX" << "\n";
  }

  out << "# NumCoef: " << pb_constraintmap.size() << "\n";

  for(std::map<literalt,unsigned>::const_iterator it=pb_constraintmap.begin();
      it!=pb_constraintmap.end();++it)
    {
      int dimacs_lit = (*it).first.dimacs();
      out << "v" << dimacs_lit << " c" << ((*it).second) << "\n";
    }

  //std::cout << "exit: No Lit. = " << no_variables () << "\n";
}

/*******************************************************************\

Function: pbs_dimacs_cnft::pbs_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool pbs_dimacs_cnft::pbs_solve()
{
  //std::cout << "solve: No Lit. = " << no_variables () << "\n";

  std::string command;

  if(!pbs_path.empty()) {
    command += pbs_path;
    if (command.substr(command.length(),1) != "/")
      command += "/";
  }

  command += "pbs";

  //std::cout << "PBS COMMAND IS: " << command << "\n";
  /*
    if (!(getenv("PBS_PATH") == NULL)) 
    {
    command = getenv("PBS_PATH");
    }
    else
    {
    error ("Unable to read PBS_PATH environment variable.\n");
    return false;
    }
  */

  command += " -f temp.cnf";

  #if 1
  if (optimize)
    {
      if (binary_search) {
	command += " -S 1000 -D 1 -H -I -a";
      }
      else {
	//std::cout << "NO BINARY SEARCH" << "\n";
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
  assert(0 == res);

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

  while(file && !file.eof ())
    {
      std::getline(file,line);
      if(strstr(line.c_str(),
		"Variable Assignments Satisfying CNF Formula:")!=NULL)
	{
	  //print ("Reading assignments...\n");
	  //std::cout << "No literals: " << no_variables() << "\n";
	  satisfied = true;
	  assigned.clear ();
	  for (size_t i = 0; (file && (i < no_variables())); ++i)
	    {
	      file >> v;
	      if (v > 0)
		{
		  //std::cout << v << " ";
		  assigned.insert(v);
		}
	    }
	  //std::cout << "\n";
	  //print ("Finished reading assignments.\n");
	}
      else if (strstr(line.c_str(),"SAT... SUM") != NULL)
	{
	  //print (line);
	  sscanf(line.c_str(),"%*s %*s %*s %d", &opt_sum);
	}
      else if (strstr(line.c_str(),"SAT - All implied") != NULL)
	{
	  //print (line);
	  sscanf(line.c_str(),"%*s %*s %*s %*s %*s %*s %*s %*s %*s %*s %*s %d", &opt_sum);
	}
      else if (strstr(line.c_str(),"SAT... Solution") != NULL)
	{
	  //print(line);
	  sscanf(line.c_str(),"%*s %*s %*s %d", &opt_sum);
	}
      else if (strstr(line.c_str(),"Optimal Soln") != NULL)
	{
	  //print(line);
	  if (strstr(line.c_str(),"time out") != NULL)
	    {
	      print (6, "WARNING:  TIMED OUT.  SOLUTION MAY BE INCORRECT.\n");
	      return satisfied;
	    }
	  sscanf(line.c_str(),"%*s %*s %*s %d", &opt_sum);
	}
    }
  
  return satisfied;
}

/*******************************************************************\

Function: pbs_dimacs_cnft::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt pbs_dimacs_cnft::prop_solve()
{
  std::ofstream file("temp.cnf");
   
  write_dimacs_cnf(file);
  
  std::ofstream pbfile("temp.cnf.pb");
  
  write_dimacs_pb(pbfile);

  file.close();
  pbfile.close();

  messaget::status() << 
    no_variables() << " variables, " <<
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
    return P_SATISFIABLE;
  else
    return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: pbs_dimacs_cnft::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt pbs_dimacs_cnft::l_get(literalt a) const
{
  int dimacs_lit = a.dimacs();
  
  //std::cout << a << " / " << dimacs_lit << " = ";

  bool neg = (dimacs_lit < 0);
  if(neg)
    dimacs_lit = -dimacs_lit;

  std::set<int>::const_iterator f = assigned.find(dimacs_lit);

  if(!neg)
    {
      if(f == assigned.end())
	{
	  //std::cout << "FALSE" << "\n";
	  return tvt(false);
	}
      else
	{
	  //std::cout << "TRUE" << "\n";
	  return tvt(true);
	}
    }
  else
    {
      if(f != assigned.end())
	{
	  //std::cout << "FALSE" << "\n";
	  return tvt(false);
	}
      else
	{
	  //std::cout << "TRUE" << "\n";
	  return tvt(true);
	}
    }

  //std::cout << "ERROR" << "\n";
  return tvt(tvt::TV_UNKNOWN);
}
