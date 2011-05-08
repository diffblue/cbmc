/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_TYPECHECK_UNESCAPE_STRING_H
#define CPROVER_C_TYPECHECK_UNESCAPE_STRING_H

#include <string>
#include <vector>

void unescape_string(
  const std::string &src,
  std::string &dest);

void unescape_wide_string(
  const std::string &src,
  std::vector<unsigned int> &dest);

#endif
