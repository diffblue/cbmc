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
  help_entry(                                                                  \
    "--document-properties-html", "generate HTML property documentation")      \
    << help_entry(                                                             \
         "--document-properties-latex",                                        \
         "generate Latex property documentation")

#endif // CPROVER_GOTO_INSTRUMENT_DOCUMENT_PROPERTIES_H
