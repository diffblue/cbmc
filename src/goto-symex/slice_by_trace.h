/*******************************************************************\

Module: Slicer for matching with trace files

Author: Alex Groce (agroce@gmail.com)

\*******************************************************************/

/// \file
/// Slicer for matching with trace files

#ifndef CPROVER_GOTO_SYMEX_SLICE_BY_TRACE_H
#define CPROVER_GOTO_SYMEX_SLICE_BY_TRACE_H

#include "symex_target_equation.h"

class symex_slice_by_tracet
{
public:
  explicit symex_slice_by_tracet(const namespacet &_ns)
    : ns(_ns),
      alphabet_parity(false),
      merge_symbol("goto_symex::\\merge", bool_typet())

  {
  }

  void slice_by_trace(
    std::string trace_files,
    symex_target_equationt &equation);

 protected:
  const namespacet &ns;
  typedef std::set<irep_idt> alphabett;
  alphabett alphabet;
  bool alphabet_parity;
  std::string semantics;

  typedef std::pair<std::set<irep_idt>, bool> event_sett;
  typedef std::vector<event_sett> event_tracet;

  event_tracet sigma;

  typedef std::vector<std::vector<irep_idt> > value_tracet;

  value_tracet sigma_vals;

  typedef std::vector<exprt> trace_conditionst;

  trace_conditionst t;

  std::set<exprt> sliced_guards;

  std::vector<exprt> merge_map_back;

  std::vector<std::pair<bool, std::set<exprt> > > merge_impl_cache_back;

  irep_idt merge_identifier;

  symbol_exprt merge_symbol;

  void read_trace(std::string filename);

  bool parse_alphabet(std::string read_line);

  void parse_events(std::string read_line);

  void compute_ts_back(symex_target_equationt &equation);

  void slice_SSA_steps(
    symex_target_equationt &equation,
    std::set<exprt> implications);

  bool matches(event_sett s, irep_idt event);

  void assign_merges(symex_target_equationt &equation);

  std::set<exprt> implied_guards(exprt e);

  bool implies_false(exprt e);
};

#endif // CPROVER_GOTO_SYMEX_SLICE_BY_TRACE_H
