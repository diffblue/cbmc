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

// clang-format off
#define HELP_DOCUMENT_PROPERTIES                                               \
  " --document-properties-html   generate HTML property documentation\n"       \
  " --document-properties-latex  generate Latex property documentation\n"

// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_DOCUMENT_PROPERTIES_H
