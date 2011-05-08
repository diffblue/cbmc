/*******************************************************************\

Module: Reading DIMACS CNF

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>

#include "read_dimacs_cnf.h"

//#define VERBOSE

/*******************************************************************\

Function: cnft::read_dimacs_cnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void read_dimacs_cnf(std::istream &in, cnft &dest)
{
#define DELIMITERS "\t\n\v\f\r "
#define CHAR_DELIMITERS "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

  bvt new_bv;
  std::string line;

  while(getline(in, line))
    {
      line += " ";
      while(true)
	{
	  if(line.empty())
	    break;
#ifdef VERBOSE
	  std::cout << "begin line " << line << std::endl;
#endif
	  size_t pos = line.find_first_of(DELIMITERS, 0);
#ifdef VERBOSE
	  std::cout << "pos " << pos << std::endl;
#endif
	  size_t pos_char = line.find_first_of(CHAR_DELIMITERS, 0);
	  if(pos != std::string::npos)
	    {
	      std::string decision = line.substr(0, pos);
	      line.erase(0,pos+1);
#ifdef VERBOSE
	      std::cout << "i am here\n";
	      std::cout << decision << std::endl;
	      std::cout << "line" << line << std::endl;
#endif
	      if(!decision.compare(std::string("c")))
		//	      if(!strcasecmp(decision.c_str(),"c"))
		{
#ifdef VERBOSE
		  std::cout << "c " << std::endl;
#endif
		  break;
		}
	      if(!decision.compare(std::string("p")))
		//	      if(!strcasecmp(decision.c_str(),"p"))
		{
#ifdef VERBOSE
		  std::cout << "p " << std::endl;
#endif
		  break;
		}
	      if(pos_char == std::string::npos) //no char present in the clause
		{
		  int parsed_lit = atoi(decision.c_str());
#ifdef VERBOSE
		  std::cout << "parsed_lit " << parsed_lit << " " << std::endl;
#endif
		  if(parsed_lit == 0) 
		    {
		      bvt no_dup;
		      cnft::eliminate_duplicates(new_bv, no_dup);
#ifdef VERBOSE
		      std::cout << "calling lcnf " << new_bv.size() << std::endl;
#endif
		      dest.lcnf(no_dup);
		      new_bv.clear();
		      no_dup.clear();
		    }
		  else
		    {
		      unsigned var = abs(parsed_lit); //because of the const variable
		      literalt l;
		      bool sign = (parsed_lit > 0) ? false : true;
		      l.set(var, sign);
#ifdef VERBOSE
		      std::cout << "setting l to " << l.get() << std::endl;
#endif
		      new_bv.push_back(l);
		      if(dest.no_variables() <= var)
			dest.set_no_variables(var+1);
		    }
		}
	    }
	}
    }
}
