/*******************************************************************\

Module: Symbolic Execution

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Exceptions that can be raised during the equation conversion phase

#ifndef CPROVER_GOTO_SYMEX_EQUATION_CONVERSION_EXCEPTIONS_H
#define CPROVER_GOTO_SYMEX_EQUATION_CONVERSION_EXCEPTIONS_H

#include <ostream>

#include <util/namespace.h>

#include <langapi/language_util.h>

#include "symex_target_equation.h"

class equation_conversion_exceptiont : public std::runtime_error
{
public:
  equation_conversion_exceptiont(
    const std::string &message,
    const symex_target_equationt::SSA_stept &step,
    const namespacet &ns)
    : runtime_error(message), step(step)
  {
    std::ostringstream error_msg;
    error_msg << runtime_error::what();
    error_msg << "\nSource GOTO statement: "
              << from_expr(ns, "java", step.source.pc->code);
    error_msg << "\nStep:\n";
    step.output(ns, error_msg);
    error_message = error_msg.str();
  }

  explicit equation_conversion_exceptiont(
    const std::string &message,
    const symex_target_equationt::SSA_stept &step)
    : equation_conversion_exceptiont(message, step, namespacet{symbol_tablet{}})
  {
  }

  const char *what() const optional_noexcept override
  {
    return error_message.c_str();
  }

private:
  symex_target_equationt::SSA_stept step;
  std::string error_message;
};

#endif // CPROVER_GOTO_SYMEX_EQUATION_CONVERSION_EXCEPTIONS_H
