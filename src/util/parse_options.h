/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_PARSE_OPTIONS_H
#define CPROVER_UTIL_PARSE_OPTIONS_H

#include <string>

#include "cmdline.h"
#include "message.h"

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

class parse_optionst: public parse_options_baset
{
public:
  parse_optionst(
    const std::string &optstring,
    int argc,
    const char **argv,
    message_handlert &message_handler):
    parse_options_baset(optstring, argc, argv),
    message(message_handler)
  {
  }

  int main() override;

protected:
  messaget message;
};

#endif // CPROVER_UTIL_PARSE_OPTIONS_H
