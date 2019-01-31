/*******************************************************************\

Module: Goto Trace Storage

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Trace Storage

#include "goto_trace_storage.h"

goto_trace_storaget::goto_trace_storaget(const namespacet &ns) : ns(ns)
{
}

const goto_tracet &goto_trace_storaget::insert(goto_tracet &&trace)
{
  traces.push_back(trace);
  const auto &last_step = traces.back().get_last_step();
  DATA_INVARIANT(
    last_step.is_assert(), "last goto trace step expected to be assertion");
  property_id_to_trace_index.emplace(last_step.property_id, traces.size() - 1);
  return traces.back();
}

const std::vector<goto_tracet> &goto_trace_storaget::all() const
{
  return traces;
}

const goto_tracet &goto_trace_storaget::
operator[](const irep_idt &property_id) const
{
  const auto trace_found = property_id_to_trace_index.find(property_id);
  PRECONDITION(trace_found != property_id_to_trace_index.end());

  return traces.at(trace_found->second);
}

const namespacet &goto_trace_storaget::get_namespace() const
{
  return ns;
}
