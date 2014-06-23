/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_TYPECHECK_UNESCAPE_STRING_H
#define CPROVER_C_TYPECHECK_UNESCAPE_STRING_H

#include <string>

void unescape_string(
  const std::string &src,
  std::string &dest);

void unescape_wide_string(
  const std::string &src,
  std::basic_string<unsigned int> &dest);

#endif
