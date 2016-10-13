/*******************************************************************\

Module: Defines identifiers for string functions

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#include <solvers/refinement/string_functions.h>

bool starts_with(irep_idt id, irep_idt prefix) {
  std::string s = id2string(id);
  std::string t = id2string(prefix);
  for(int i = 0; i < t.length(); i++)
    if(s[i] != t[i]) return false;
  return true;
}
