/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_IDENTIFIER_H
#define CPROVER_UTIL_IDENTIFIER_H

#include <string>
#include <vector>

#define ID_SEPARATOR "::"

class identifiert
{
public:
  explicit identifiert(const std::string &s)
  { parse(s); }

  identifiert()
  { }

  std::string as_string() const;

  using componentst = std::vector<std::string>;
  componentst components;

protected:
  void parse(const std::string &s);
};

#endif // CPROVER_UTIL_IDENTIFIER_H
