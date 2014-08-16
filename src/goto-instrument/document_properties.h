/*******************************************************************\

Module: Documentation of Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iosfwd>

#include <goto-programs/goto_functions.h>

void document_properties_latex(
  const goto_functionst &goto_functions,
  std::ostream &out);

void document_properties_html(
  const goto_functionst &goto_functions,
  std::ostream &out);
