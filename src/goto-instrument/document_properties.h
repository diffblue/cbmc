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

#define OPT_DOCUMENT_PROPERTIES                                                \
  "(document-claims-latex)(document-claims-html)"                              \
  "(document-properties-latex)(document-properties-html)"

#define HELP_DOCUMENT_PROPERTIES                                               \
  " {y--document-properties-html} \t generate HTML property documentation\n"   \
  " {y--document-properties-latex} \t generate LaTeX property documentation\n"

#endif // CPROVER_GOTO_INSTRUMENT_DOCUMENT_PROPERTIES_H
