/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Safety Checker Interface

#ifndef CPROVER_GOTO_PROGRAMS_SAFETY_CHECKER_H
#define CPROVER_GOTO_PROGRAMS_SAFETY_CHECKER_H

// this is just an interface -- it won't actually do any checking!

#include <util/invariant.h>
#include <util/message.h>

#include "goto_trace.h"
#include "goto_functions.h"

class safety_checkert:public messaget
{
public:
  explicit safety_checkert(
    const namespacet &_ns);

  explicit safety_checkert(
    const namespacet &_ns,
    message_handlert &_message_handler);

  enum class resultt { SAFE, UNSAFE, ERROR };

  // check whether all assertions in goto_functions are safe
  // if UNSAFE, then a trace is returned

  virtual resultt operator()(
    const goto_functionst &goto_functions)=0;

  // this is the counterexample
  goto_tracet error_trace;

protected:
  // the namespace
  const namespacet &ns;
};

/// \brief The worst of two results
inline safety_checkert::resultt &
operator&=(safety_checkert::resultt &a, safety_checkert::resultt const &b)
{
  switch(a)
  {
  case safety_checkert::resultt::ERROR:
    return a;
  case safety_checkert::resultt::SAFE:
    a = b;
    return a;
  case safety_checkert::resultt::UNSAFE:
    a = b == safety_checkert::resultt::ERROR ? b : a;
    return a;
  }
  UNREACHABLE;
}

/// \brief The best of two results
inline safety_checkert::resultt &
operator|=(safety_checkert::resultt &a, safety_checkert::resultt const &b)
{
  switch(a)
  {
  case safety_checkert::resultt::SAFE:
    return a;
  case safety_checkert::resultt::ERROR:
    a = b;
    return a;
  case safety_checkert::resultt::UNSAFE:
    a = b == safety_checkert::resultt::SAFE ? b : a;
    return a;
  }
  UNREACHABLE;
}
#endif // CPROVER_GOTO_PROGRAMS_SAFETY_CHECKER_H
