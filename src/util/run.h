/*******************************************************************\

Module:

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/


#ifndef CPROVER_UTIL_RUN_H
#define CPROVER_UTIL_RUN_H

#include <string>
#include <vector>

int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output);

int run_shell(const std::string &command);

#endif // CPROVER_UTIL_RUN_H
