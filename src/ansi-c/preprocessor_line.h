/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Conversion

#ifndef CPROVER_ANSI_C_PREPROCESSOR_LINE_H
#define CPROVER_ANSI_C_PREPROCESSOR_LINE_H

class parsert;

void preprocessor_line(
  const char *text,
  parsert &parser);

#endif // CPROVER_ANSI_C_PREPROCESSOR_LINE_H
