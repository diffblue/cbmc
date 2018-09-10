/*******************************************************************\

Module:

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/


#ifndef CPROVER_UTIL_RUN_H
#define CPROVER_UTIL_RUN_H

#include <iosfwd>
#include <string>
#include <vector>

int run(const std::string &what, const std::vector<std::string> &argv);

int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output,
  const std::string &std_error);

/// A variant that streams the stdout of the child into an ostream
int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  std::ostream &std_output,
  const std::string &std_error);

#endif // CPROVER_UTIL_RUN_H
