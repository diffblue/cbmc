/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_PARSE_OPTIONS_H
#define CPROVER_UTIL_PARSE_OPTIONS_H

#include <string>

#include "cmdline.h"

class parse_options_baset
{
public:
  parse_options_baset(
    const std::string &optstring, int argc, const char **argv);

  cmdlinet cmdline;

  virtual void help();
  virtual void usage_error();

  virtual int doit()=0;

  virtual int main();
  virtual ~parse_options_baset() { }

private:
  void unknown_option_msg();
  bool parse_result;
};

#endif // CPROVER_UTIL_PARSE_OPTIONS_H
