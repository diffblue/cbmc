/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CMDLINE_H
#define CPROVER_CMDLINE_H

#include <vector>
#include <list>
#include <string>

class cmdlinet
{
public:
  virtual bool parse(int argc, const char **argv, const char *optstring);

  const char *getval(char option) const;
  const char *getval(const char *option) const;
  const std::list<std::string> &get_values(const std::string &option) const;
  const std::list<std::string> &get_values(char option) const;

  virtual bool isset(char option) const;
  virtual bool isset(const char *option) const;
  virtual void set(const std::string &option);
  virtual void set(const std::string &option, const std::string &value);
  virtual void clear();

  typedef std::vector<std::string> argst;
  argst args;
  
  cmdlinet();
  virtual ~cmdlinet();
  
protected:
  struct optiont
  {
    bool isset, hasval, islong;
    char optchar;
    std::string optstring;
    std::list<std::string> values;
  };
   
  std::vector<optiont> options;

  int getoptnr(char option) const;
  int getoptnr(const std::string &option) const;
};

#endif
