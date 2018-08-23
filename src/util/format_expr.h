/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORMAT_EXPR_H
#define CPROVER_UTIL_FORMAT_EXPR_H

#include "expr.h"
#include "format.h"

class codet;

//! Formats an expression in a generic syntax
//! that is inspired by C/C++/Java, and is meant for debugging
std::ostream &format_rec(std::ostream &, const exprt &);
std::ostream &format_rec(std::ostream &, const codet &);

#endif // CPROVER_UTIL_FORMAT_EXPR_H
