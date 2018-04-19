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

class guard_conversion_exceptiont : public std::runtime_error
{
public:
  guard_conversion_exceptiont(
    const symex_target_equationt::SSA_stept &step,
    const namespacet &ns)
    : runtime_error("Error converting guard for step"), step(step)
  {
    std::ostringstream error_msg;
    error_msg << runtime_error::what();
    error_msg << "\nSource GOTO statement: "
              << from_expr(ns, "java", step.source.pc->code);
    error_msg << "\nStep:\n";
    step.output(ns, error_msg);
    error_message = error_msg.str();
  }

  explicit guard_conversion_exceptiont(
    const symex_target_equationt::SSA_stept &step)
    : guard_conversion_exceptiont(step, namespacet{symbol_tablet{}})
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
