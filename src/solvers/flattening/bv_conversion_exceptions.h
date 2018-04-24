/*******************************************************************\

Module: Bit vector conversion

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Exceptions that can be raised in bv_conversion

#ifndef CPROVER_SOLVERS_FLATTENING_BV_CONVERSION_EXCEPTIONS_H
#define CPROVER_SOLVERS_FLATTENING_BV_CONVERSION_EXCEPTIONS_H

#include <stdexcept>
#include <string>

#include <util/expr.h>

class bitvector_conversion_exceptiont : public std::runtime_error
{
public:
  bitvector_conversion_exceptiont(
    const std::string &exception_message,
    const exprt &bv_expr)
    : runtime_error(exception_message), bv_expr(bv_expr)
  {
  }

private:
  exprt bv_expr;
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_CONVERSION_EXCEPTIONS_H
