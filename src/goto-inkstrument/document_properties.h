/*******************************************************************\

Module: Documentation of Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Documentation of Properties

#ifndef CPROVER_GOTO_INSTRUMENT_DOCUMENT_PROPERTIES_H
#define CPROVER_GOTO_INSTRUMENT_DOCUMENT_PROPERTIES_H

#include <iosfwd>

class goto_modelt;

void document_properties_latex(
  const goto_modelt &,
  std::ostream &out);

void document_properties_html(
  const goto_modelt &,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_DOCUMENT_PROPERTIES_H
