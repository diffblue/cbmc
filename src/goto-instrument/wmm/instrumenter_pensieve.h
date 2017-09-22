/*******************************************************************\

Module: Instrumenter

Author:

\*******************************************************************/

/// \file
/// Instrumenter

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_INSTRUMENTER_PENSIEVE_H
#define CPROVER_GOTO_INSTRUMENT_WMM_INSTRUMENTER_PENSIEVE_H

#include "event_graph.h"
#include "goto2graph.h"

class goto_modelt;
class namespacet;

class instrumenter_pensievet:public instrumentert
{
public:
  instrumenter_pensievet(goto_modelt &_goto_model, messaget &message)
    : instrumentert(_goto_model, message)
  {
  }

  void collect_pairs_naive(namespacet &ns)
  {
    egraph.collect_pairs_naive(ns);
  }

  /* collects directly all the pairs in the graph */
  void collect_pairs(namespacet &ns)
  {
    egraph.collect_pairs(ns);
  }
};

#endif // CPROVER_GOTO_INSTRUMENT_WMM_INSTRUMENTER_PENSIEVE_H
