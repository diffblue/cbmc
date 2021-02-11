/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORMAT_EXPR_H
#define CPROVER_UTIL_FORMAT_EXPR_H

#include "format.h"
#include "irep.h"

#include <functional>

class exprt;

//! Formats an expression in a generic syntax
//! that is inspired by C/C++/Java, and is meant for debugging
std::ostream &format_rec(std::ostream &, const exprt &);

/// Adds a formatter for expressions with the given ID at runtime.
/// The formatter is given as a function that receives the output
/// stream and the expression as arguments.
void add_format_hook(
  irep_idt,
  std::function<std::ostream &(std::ostream &, const exprt &)>);

#endif // CPROVER_UTIL_FORMAT_EXPR_H
