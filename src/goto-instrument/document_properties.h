/*******************************************************************\

Module: Documentation of Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include <goto-programs/goto_functions.h>

void document_properties_latex(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out);

void document_properties_html(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out);
