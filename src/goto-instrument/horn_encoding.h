/*******************************************************************\

Module: Horn-clause Encoding

Author:

\*******************************************************************/

#ifndef CPROVER_HORN_ENCODING_H
#define CPROVER_HORN_ENCODING_H

#include <iosfwd>

#include <goto-programs/goto_functions.h>

void horn_encoding(
  const goto_functionst &,
  const namespacet &,
  std::ostream &out);

#endif
