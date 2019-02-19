/*******************************************************************\

Module: Goto Trace Storage

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Trace Storage

#ifndef CPROVER_GOTO_CHECKER_GOTO_TRACE_STORAGE_H
#define CPROVER_GOTO_CHECKER_GOTO_TRACE_STORAGE_H

#include <goto-programs/goto_trace.h>

class goto_trace_storaget
{
public:
  explicit goto_trace_storaget(const namespacet &);
  goto_trace_storaget(const goto_trace_storaget &) = delete;

  /// Store trace that ends in a violated assertion
  const goto_tracet &insert(goto_tracet &&);

  /// Store trace that contains multiple violated assertions
  /// \note Only property IDs that are not part of any already stored trace
  ///   are mapped to the given trace.
  const goto_tracet &insert_all(goto_tracet &&);

  const std::vector<goto_tracet> &all() const;
  const goto_tracet &operator[](const irep_idt &property_id) const;

  const namespacet &get_namespace() const;

protected:
  /// the namespace related to the traces
  const namespacet &ns;

  /// stores the traces
  std::vector<goto_tracet> traces;

  // maps property ID to index in traces
  std::unordered_map<irep_idt, std::size_t> property_id_to_trace_index;
};

#endif // CPROVER_GOTO_CHECKER_GOTO_TRACE_STORAGE_H
