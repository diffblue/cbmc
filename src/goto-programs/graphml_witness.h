/*******************************************************************\

Module: Witnesses for Traces and Proofs

Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H
#define CPROVER_GOTO_PROGRAMS_GRAPHML_WITNESS_H

#include <xmllang/graphml.h>

#include "goto_trace.h"

class graphml_witnesst
{
public:
  explicit graphml_witnesst(const namespacet &_ns)
    : ns(_ns)
  {
  }

  void operator()(const goto_tracet &goto_trace);

  inline const graphmlt &graph()
  {
    return graphml;
  }

protected:
  const namespacet &ns;
  graphmlt graphml;

  void remove_l0_l1(exprt &expr);
  std::string convert_assign_rec(
    const irep_idt &identifier,
    const code_assignt &assign);

};

#endif
