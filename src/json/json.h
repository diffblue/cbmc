/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JSON_H
#define CPROVER_JSON_H

#include <vector>
#include <map>
#include <iosfwd>
#include <string>

class jsont
{
public:
  enum { J_STRING, J_NUMBER, J_OBJECT, J_ARRAY,
         J_TRUE, J_FALSE, J_NULL } kind;

  typedef std::vector<jsont> arrayt;
  arrayt array;
  
  typedef std::map<std::string, jsont> objectt;
  objectt object;

  std::string value;

  inline void output(std::ostream &out) const
  {
    output_rec(out, 0);
  }
  
protected:
  void output_rec(std::ostream &, unsigned indent) const;
  static void escape_string(const std::string &, std::ostream &);
};

static inline std::ostream & operator << (std::ostream &out, const jsont &src)
{
  src.output(out);
  return out;
}

#endif
