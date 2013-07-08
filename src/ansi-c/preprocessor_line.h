/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_LANGUAGE_PREPROCESSOR_LINE_H
#define CPROVER_ANSI_C_LANGUAGE_PREPROCESSOR_LINE_H

class parsert;

void preprocessor_line(
  const char *text,
  parsert &parser);

#endif
