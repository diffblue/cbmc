/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_LANGUAGE_PREPROCESSOR_LINE_H
#define CPROVER_ANSI_C_LANGUAGE_PREPROCESSOR_LINE_H

#include <string>

#include <irep.h>

void preprocessor_line(
  const char *text,
  unsigned &line_no,
  irep_idt &file_name);

#endif
