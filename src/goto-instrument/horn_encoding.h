/*******************************************************************\

Module: Horn-clause Encoding

Author:

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#ifndef CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
#define CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H

#include <iosfwd>

#include <goto-programs/goto_functions.h>

void horn_encoding(
  const goto_functionst &,
  const namespacet &,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
