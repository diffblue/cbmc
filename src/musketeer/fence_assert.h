/*******************************************************************\

Module: ILP construction for cycles affecting user-assertions 
        and resolution

Author: Vincent Nimal

\*******************************************************************/

#ifndef CPROVER_FENCE_ASSERT_H
#define CPROVER_FENCE_ASSERT_H

#include <set>

#include <goto-instrument/wmm/event_graph.h>

#include "fence_inserter.h"

class instrumentert;

class fence_assert_insertert : public fence_insertert
{
protected:
  std::set<unsigned> selected_cycles;

  bool find_assert(const event_grapht::critical_cyclet &cycle) const;

  // overload for base class
  virtual void process_cycles_selection();

  // overload for base class
  virtual bool filter_cycles(unsigned cycles_id) const
  {
    return selected_cycles.find(cycles_id)!=selected_cycles.end();
  }

public:
  explicit fence_assert_insertert(instrumentert &instr):
    fence_insertert(instr)
  {
  }

  fence_assert_insertert(instrumentert &instr, memory_modelt _model):
    fence_insertert(instr, model)
  {
  }
};

#endif
