/*******************************************************************\

Module:

Author: Alex Groce

\*******************************************************************/

#include <stdlib.h>
#include <string.h>

#include <fstream>
#include <iostream>

#include <str_getline.h>
#include <i2string.h>

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

  //std::cout << "enter: No Lit. = " << no_variables () << std::endl;

  for(std::map<literalt,unsigned>::const_iterator it=pb_constraintmap.begin();
      it != pb_constraintmap.end (); ++it) {
    d_sum += ((*it).second);
  }

  if (!optimize) {
    out << "# PBType: E" << std::endl;
    out << "# PBGoal: " << goal << std::endl;
  } else if (!maximize) {
    out << "# PBType: SE" << std::endl;
    out << "# PBGoal: " << d_sum << std::endl;
    out << "# PBObj : MIN" << std::endl;
  } else {
    out << "# PBType: GE" << std::endl;
    out << "# PBGoal: " << 0 << std::endl;
    out << "# PBObj : MAX" << std::endl;
  }
  out << "# NumCoef: " << pb_constraintmap.size() << std::endl;

  for(std::map<literalt,unsigned>::const_iterator it=pb_constraintmap.begin();
      it!=pb_constraintmap.end();++it)
    {
      int dimacs_lit = (*it).first.dimacs();
      out << "v" << dimacs_lit << " c" << ((*it).second) << std::endl;
    }

  //std::cout << "exit: No Lit. = " << no_variables () << std::endl;
}

/*******************************************************************\

Function: pbs_dimacs_cnft::pbs_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool pbs_dimacs_cnft::pbs_solve()
{
  //std::cout << "solve: No Lit. = " << no_variables () << std::endl;

  std::string command;

  if(!pbs_path.empty()) {
    command += pbs_path;
    if (command.substr(command.length(),1) != "/")
      command += "/";
  }

  command += "pbs";

  //std::cout << "PBS COMMAND IS: " << command << std::endl;
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
	//std::cout << "NO BINARY SEARCH" << std::endl;
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

  system(command.c_str());

  std::ifstream file("temp.out");
  std::string line;
  int v;
  bool satisfied = false;

  if(file.fail())
    {
      error("Unable to read SAT results!\n");
      return false;
    }
   
  opt_sum = -1;

  while(file && !file.eof ())
    {
      str_getline(file,line);
      if(strstr(line.c_str(),
		"Variable Assignments Satisfying CNF Formula:")!=NULL)
	{
	  //print ("Reading assignments...\n");
	  //std::cout << "No literals: " << no_variables() << std::endl;
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
	  //std::cout << std::endl;
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

  std::string msg=
    i2string(no_variables())+" variables, "+
    i2string(clauses.size())+" clauses";
  messaget::status(msg);

  bool result=pbs_solve();
  
  if (!result)
    {
      msg="PBS checker: system is UNSATISFIABLE";
    }
  else
    {
      msg="PBS checker: system is SATISFIABLE"; 
      if (optimize)
	msg += " (distance " + i2string(opt_sum) + ")";
    }
  
  messaget::status(msg);

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
	  //std::cout << "FALSE" << std::endl;
	  return tvt(false);
	}
      else
	{
	  //std::cout << "TRUE" << std::endl;
	  return tvt(true);
	}
    }
  else
    {
      if(f != assigned.end())
	{
	  //std::cout << "FALSE" << std::endl;
	  return tvt(false);
	}
      else
	{
	  //std::cout << "TRUE" << std::endl;
	  return tvt(true);
	}
    }

  //std::cout << "ERROR" << std::endl;
  return tvt(tvt::TV_UNKNOWN);
}
