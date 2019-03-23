/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

// THIS HEADER IS DEPRECATED (since 2015-06-30) AND WILL GO AWAY

#ifndef CPROVER_UTIL_LISPEXPR_H
#define CPROVER_UTIL_LISPEXPR_H

#if defined(_WIN32) && !defined(__MINGW32__)
#include <cstring>
#define strcasecmp _strcmpi
#else
#include <strings.h>
#endif

#include <string>
#include <vector>
#include <iosfwd>

class lispsymbolt:public std::string
{
 public:
  // NOLINTNEXTLINE(runtime/explicit)
  lispsymbolt(const char *a):std::string(a)
  {
  }

  lispsymbolt():std::string()
  {
  }

  // NOLINTNEXTLINE(runtime/explicit)
  lispsymbolt(const std::string &a):std::string(a)
  {
  }

  bool operator== (const lispsymbolt &b) const
  { return strcasecmp(c_str(), b.c_str())==0; }

  bool operator!= (const lispsymbolt &b) const
  { return strcasecmp(c_str(), b.c_str())!=0; }

  bool operator== (const char *b) const
  { return strcasecmp(c_str(), b)==0; }

  bool operator!= (const char *b) const
  { return strcasecmp(c_str(), b)!=0; }
};

inline bool operator== (const char *a, const lispsymbolt &b)
{ return strcasecmp(a, b.c_str())==0; }

inline bool operator!= (const char *a, const lispsymbolt &b)
{ return strcasecmp(a, b.c_str())!=0; }

inline bool operator== (const lispsymbolt &a, const std::string &b)
{ return strcasecmp(a.c_str(), b.c_str())==0; }

inline bool operator!= (const lispsymbolt &a, const std::string &b)
{ return strcasecmp(a.c_str(), b.c_str())!=0; }

inline bool operator== (const std::string &a, const lispsymbolt &b)
{ return strcasecmp(a.c_str(), b.c_str())==0; }

inline bool operator!= (const std::string &a, const lispsymbolt &b)
{ return strcasecmp(a.c_str(), b.c_str())!=0; }

class lispexprt:public std::vector<lispexprt>
{
public:
  enum { String, Symbol, Number, List } type;
  lispsymbolt value;
  std::string expr2string() const;
  bool parse(const std::string &s);
  bool is_nil() const
  { return type==Symbol && value=="nil"; }

  void make_nil()
  {
    clear();
    type=Symbol;
    value="nil";
  }

protected:
  bool parse(const std::string &s, std::string::size_type &ptr);
};

inline std::ostream &operator<<(
  std::ostream &out,
  const lispexprt &expr)
{
  return out << expr.expr2string();
}

int test_lispexpr();

#endif // CPROVER_UTIL_LISPEXPR_H
