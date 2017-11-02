/*******************************************************************\

Module: Witnesses for Traces and Proofs

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Witnesses for Traces and Proofs

#ifndef CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H
#define CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H

#include <xmllang/graphml.h>

#include <goto-symex/symex_target_equation.h>

#include "goto_trace.h"

class graphml_witnesst
{
public:
  explicit graphml_witnesst(const namespacet &_ns)
    : ns(_ns)
  {
  }

  void operator()(const goto_tracet &goto_trace);
  void operator()(const symex_target_equationt &equation);

  const graphmlt &graph()
  {
    return graphml;
  }

private:
  const namespacet &ns;
  graphmlt graphml;
};

#endif // CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H
