/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_CMDLINE_H
#define CPROVER_UTIL_CMDLINE_H

#include <vector>
#include <list>
#include <string>

#include "optional.h"

class cmdlinet
{
public:
  virtual bool parse(int argc, const char **argv, const char *optstring);

  std::string get_value(char option) const;
  std::string get_value(const char *option) const;

  const std::list<std::string> &get_values(const std::string &option) const;
  const std::list<std::string> &get_values(char option) const;

  std::list<std::string> get_comma_separated_values(const char *option) const;

  virtual bool isset(char option) const;
  virtual bool isset(const char *option) const;
  virtual void set(const std::string &option);
  virtual void set(const std::string &option, const std::string &value);
  virtual void clear();

  typedef std::vector<std::string> argst;
  argst args;
  std::string unknown_arg;

  cmdlinet();
  virtual ~cmdlinet();

protected:
  struct optiont
  {
    bool isset;
    bool hasval;
    bool islong;
    char optchar;
    std::string optstring;
    std::list<std::string> values;
  public:
    optiont():
      isset(false),
      hasval(false),
      islong(false),
      optchar(0)
    {}
  };

  std::vector<optiont> options;

  optionalt<std::size_t> getoptnr(char option) const;
  optionalt<std::size_t> getoptnr(const std::string &option) const;
};

#endif // CPROVER_UTIL_CMDLINE_H
