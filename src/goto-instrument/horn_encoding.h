/*******************************************************************\

Module: Horn-clause Encoding

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#ifndef CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
#define CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H

#include <iosfwd>

class goto_modelt;

void horn_encoding(
  const goto_modelt &,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
