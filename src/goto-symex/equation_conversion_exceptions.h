/*******************************************************************\

Module: Symbolic Execution

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Exceptions that can be raised during the equation conversion phase

#ifndef CPROVER_GOTO_SYMEX_EQUATION_CONVERSION_EXCEPTIONS_H
#define CPROVER_GOTO_SYMEX_EQUATION_CONVERSION_EXCEPTIONS_H

#include <sstream>

#include <util/format_expr.h>

#include "symex_target_equation.h"

class equation_conversion_exceptiont : public std::runtime_error
{
public:
  equation_conversion_exceptiont(
    const std::string &message,
    const SSA_stept &step)
    : runtime_error(message), step(step)
  {
    std::ostringstream error_msg;
    error_msg << runtime_error::what();
    error_msg << "\nSource GOTO statement: " << format(step.source.pc->code);
    error_msg << "\nStep:\n";
    step.output(error_msg);
    error_message = error_msg.str();
  }

  const char *what() const optional_noexcept override
  {
    return error_message.c_str();
  }

private:
  SSA_stept step;
  std::string error_message;
};

#endif // CPROVER_GOTO_SYMEX_EQUATION_CONVERSION_EXCEPTIONS_H
