/*******************************************************************\

Module: cycles visitor for computing edges involved for fencing

Author: Vincent Nimal

\*******************************************************************/

#ifndef CYCLES_VISITOR_H
#define CYCLES_VISITOR_H

#include <set>

#include <goto-instrument/wmm/event_graph.h>

class fence_insertert;

class cycles_visitort
{
protected:
  typedef event_grapht::critical_cyclet::delayt edget;

  fence_insertert& fence_inserter;

public:
  cycles_visitort(fence_insertert& _fi)
    : fence_inserter(_fi)
  {}

  /* computes po^+ edges in U{C_1, ..., C_j} */
  void po_edges(std::set<unsigned>& edges);

  /* computes pairs that will be protected for the 
     TSO/PSO/RMO/Power/ARM by the constraints */
  void powr_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void poww_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void porw_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void porr_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void com_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
};

#endif
