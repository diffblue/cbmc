/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LISPEXPR_H
#define CPROVER_LISPEXPR_H

#if defined(_WIN32) && !defined(__MINGW32__)
#include <cstring>
#define strcasecmp _strcmpi
#else
#include <strings.h>
#endif

#include <string>
#include <vector>
#include <ostream>

class lispsymbolt:public std::string
{
 public:
  lispsymbolt(const char *a):std::string(a)
  {
  }
 
  lispsymbolt():std::string()
  {
  }
 
  lispsymbolt(const std::string &a):std::string(a)
  {
  }
 
  friend bool operator== (const lispsymbolt &a, const lispsymbolt &b)
  { return strcasecmp(a.c_str(), b.c_str())==0; }

  friend bool operator!= (const lispsymbolt &a, const lispsymbolt &b)
  { return strcasecmp(a.c_str(), b.c_str())!=0; }

  friend bool operator== (const lispsymbolt &a, const char *b)
  { return strcasecmp(a.c_str(), b)==0; }

  friend bool operator!= (const lispsymbolt &a, const char *b)
  { return strcasecmp(a.c_str(), b)!=0; }

  friend bool operator== (const char *a, const lispsymbolt &b)
  { return strcasecmp(a, b.c_str())==0; }

  friend bool operator!= (const char *a, const lispsymbolt &b)
  { return strcasecmp(a, b.c_str())!=0; }

  friend bool operator== (const lispsymbolt &a, const std::string &b)
  { return strcasecmp(a.c_str(), b.c_str())==0; }

  friend bool operator!= (const lispsymbolt &a, const std::string &b)
  { return strcasecmp(a.c_str(), b.c_str())!=0; }

  friend bool operator== (const std::string &a, const lispsymbolt &b)
  { return strcasecmp(a.c_str(), b.c_str())==0; }

  friend bool operator!= (const std::string &a, const lispsymbolt &b)
  { return strcasecmp(a.c_str(), b.c_str())!=0; }
};

class lispexprt:public std::vector<lispexprt>
{
 public:
  enum { String, Symbol, Number, List } type;
  lispsymbolt value;
  std::string expr2string() const;
  bool parse(const std::string &s, unsigned &ptr);
  bool parse(const std::string &s);
  bool is_nil() const
  { return type==Symbol && value=="nil"; }
   
  void make_nil()
  {
    clear();
    type=Symbol;
    value="nil";
  }

  friend std::ostream& operator<< (std::ostream& out, const lispexprt &expr)
  {
    out << expr.expr2string();
    return out;
  }
};
 
std::string escape(const std::string &s);

int test_lispexpr();

#endif
