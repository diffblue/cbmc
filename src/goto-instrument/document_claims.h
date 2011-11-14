/*******************************************************************\

Module: Claim Documentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <goto-programs/goto_functions.h>

void document_claims_latex(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out);

void document_claims_html(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out);
