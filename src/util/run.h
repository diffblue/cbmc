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

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin, stdout and stderr may be redirected from/to a given file.
/// Give the empty string to retain the default handle.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output,
  const std::string &std_error);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin and stderr may be redirected from/to a given file.
/// Give the empty string to retain the default handle.
/// Any output to stdout is stored in the \p std_output stream buffer.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  std::ostream &std_output,
  const std::string &std_error);

#endif // CPROVER_UTIL_RUN_H
