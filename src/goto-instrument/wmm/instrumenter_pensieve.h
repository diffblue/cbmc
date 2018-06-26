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

  void collect_pairs_naive()
  {
    egraph.collect_pairs_naive();
  }

  /* collects directly all the pairs in the graph */
  void collect_pairs()
  {
    egraph.collect_pairs();
  }
};

#endif // CPROVER_GOTO_INSTRUMENT_WMM_INSTRUMENTER_PENSIEVE_H
