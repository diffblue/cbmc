/*******************************************************************\

Module: Horn-clause Encoding

Author:

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#ifndef CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
#define CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H

#include <iosfwd>

#include <goto-programs/goto_model.h>

enum horn_formatt
{
  ASCII,
  SMT2
};

void horn_encoding(const goto_modelt &, horn_formatt, std::ostream &);

#endif // CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
