/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_PARSE_OPTIONS_H
#define CPROVER_UTIL_PARSE_OPTIONS_H

#include <string>

#include "cmdline.h"

// Forwards declare messaget so we can use references to it
class messaget;

class parse_options_baset
{
public:
  parse_options_baset(
    const std::string &optstring,
    int argc,
    const char **argv,
    messaget &l);

  cmdlinet cmdline;

  virtual void help();
  virtual void usage_error();

  virtual int doit()=0;

  virtual int main();
  virtual ~parse_options_baset() { }

protected:
  messaget &log;

private:
  void unknown_option_msg();
  bool parse_result;
};

std::string
banner_string(const std::string &front_end, const std::string &version);

/// Utility for displaying help centered messages borderered by "* *"
/// - we use this for displaying banner information and the like
/// in help messages
/// \example
///   align_center_with_border("test-text")
///   == "* *                        test-text                        * *"
std::string align_center_with_border(const std::string &text);

#endif // CPROVER_UTIL_PARSE_OPTIONS_H
