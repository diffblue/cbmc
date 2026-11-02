/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory models for partial order concurrency

#ifndef CPROVER_GOTO_SYMEX_MEMORY_MODEL_H
#define CPROVER_GOTO_SYMEX_MEMORY_MODEL_H

#include "partial_order_concurrency.h"

class memory_model_baset : public partial_order_concurrencyt
{
public:
  explicit memory_model_baset(const namespacet &_ns);
  virtual ~memory_model_baset();

  virtual void operator()(symex_target_equationt &, message_handlert &) = 0;

  /// Prepare event lists and clock types without adding constraints.
  /// Call this before using the staged constraint methods.
  void prepare(symex_target_equationt &equation, message_handlert &mh)
  {
    build_event_lists(equation, mh);
    build_clock_type();
  }

  /// Add init writes for shared variables without building the full
  /// event lists. Used by --refine-concurrency to include init writes
  /// in the equation before solver conversion, while deferring the
  /// ordering constraints to the refinement loop.
  void add_init_writes_only(symex_target_equationt &equation)
  {
    add_init_writes(equation);
  }

  /// Staged constraint addition for incremental refinement.
  /// Each stage adds more constraints; earlier stages are cheaper.
  enum class refinement_staget
  {
    READ_FROM,
    PROGRAM_ORDER,
    WRITE_SERIALIZATION,
    FROM_READ
  };

  /// Add constraints for a specific refinement stage.
  virtual void
  add_stage(refinement_staget stage, symex_target_equationt &equation) = 0;

protected:
  /// In-thread program order
  /// \param e1: preceding event
  /// \param e2: following event
  /// \return true if e1 precedes e2 in program order
  bool po(event_it e1, event_it e2);

  // produce fresh symbols
  unsigned var_cnt;
  symbol_exprt nondet_bool_symbol(const std::string &prefix);

  // This gives us the choice symbol for an R-W pair;
  // built by the method below.
  typedef std::map<std::pair<event_it, event_it>, symbol_exprt> choice_symbolst;
  choice_symbolst choice_symbols;

  /// For each read `r` from every address we collect the choice symbols `S`
  ///   via \ref register_read_from_choice_symbol (for potential read-write
  ///   pairs) and add a constraint r.guard => \/S.
  /// \param equation: symex equation where the new constraint should be added
  void read_from(symex_target_equationt &equation);

  /// Introduce a new choice symbol `s` for the pair (\p r, \p w)
  /// add constraint s => (w.guard /\ r.lhs=w.lhs)
  /// add constraint s => before(w,r) [if \p w is from another thread]
  /// \param r: read event
  /// \param w: write event
  /// \param equation: symex equation where the new constraints should be added
  /// \param alias_cond: additional alias condition guard (default: true)
  /// \return the new choice symbol
  symbol_exprt register_read_from_choice_symbol(
    const event_it &r,
    const event_it &w,
    symex_target_equationt &equation,
    const exprt &alias_cond = true_exprt{});

  // maps thread numbers to an event list
  typedef std::map<unsigned, event_listt> per_thread_mapt;
};

#endif // CPROVER_GOTO_SYMEX_MEMORY_MODEL_H
