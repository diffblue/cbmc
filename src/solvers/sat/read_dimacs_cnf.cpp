/*******************************************************************\

Module: Reading DIMACS CNF

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Reading DIMACS CNF

#include <istream>
#include <cstdlib> // for abs()

#include <util/string2int.h>

#include "read_dimacs_cnf.h"

// #define VERBOSE

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
      std::cout << "begin line " << line << '\n';
      #endif
      size_t pos = line.find_first_of(DELIMITERS, 0);
      #ifdef VERBOSE
      std::cout << "pos " << pos << '\n';
      #endif
      size_t pos_char = line.find_first_of(CHAR_DELIMITERS, 0);

      if(pos!=std::string::npos)
      {
        std::string decision = line.substr(0, pos);
        line.erase(0, pos+1);
        #ifdef VERBOSE
        std::cout << "i am here\n";
        std::cout << decision << '\n';
        std::cout << "line" << line << '\n';
        #endif
        if(!decision.compare(std::string("c")))
        {
          #ifdef VERBOSE
          std::cout << "c \n";
          #endif
          break;
        }

        if(!decision.compare(std::string("p")))
        {
          #ifdef VERBOSE
          std::cout << "p \n";
          #endif
          break;
        }

        if(pos_char == std::string::npos) // no char present in the clause
        {
          int parsed_lit = unsafe_string2int(decision);
          #ifdef VERBOSE
          std::cout << "parsed_lit " << parsed_lit << " \n";
          #endif
          if(parsed_lit == 0)
          {
            bvt no_dup=cnft::eliminate_duplicates(new_bv);
            #ifdef VERBOSE
            std::cout << "calling lcnf " << new_bv.size() << '\n';
            #endif
            dest.lcnf(no_dup);
            new_bv.clear();
            no_dup.clear();
          }
          else
          {
            unsigned var = abs(parsed_lit); // because of the const variable
            literalt l;
            bool sign = (parsed_lit > 0) ? false : true;
            l.set(var, sign);
            #ifdef VERBOSE
            std::cout << "setting l to " << l.get() << '\n';
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
