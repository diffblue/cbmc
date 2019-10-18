// Copyright 2016-2019 Diffblue Limited. All Rights Reserved.

#ifndef CPROVER_GOTO_SYMEX_SYMEX_COMPLEXITY_LIMIT_EXCEEDED_ACTION_H
#define CPROVER_GOTO_SYMEX_SYMEX_COMPLEXITY_LIMIT_EXCEEDED_ACTION_H

#include "complexity_limiter.h"
#include "complexity_violation.h"
#include <util/std_expr.h>

/// Default heuristic transformation that cancels branches when complexity
/// has been breached.
class symex_complexity_limit_exceeded_actiont
{
public:
  virtual void transform(
    const complexity_violationt heuristic_result,
    goto_symex_statet &current_state)
  {
    current_state.reachable = false;
  }
  virtual ~symex_complexity_limit_exceeded_actiont()
  {
  }
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_COMPLEXITY_LIMIT_EXCEEDED_ACTION_H
