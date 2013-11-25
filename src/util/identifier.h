/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IDENTIFIER_H
#define CPROVER_IDENTIFIER_H

#include <string>
#include <vector>

#define ID_SEPARATOR "::"

class identifiert
{
public:
  identifiert(const std::string &s)
  { parse(s); }

  identifiert()
  { }

  std::string as_string() const;

  typedef std::vector<std::string> componentst;
  componentst components;

protected:
  void parse(const std::string &s);  
};

#endif
