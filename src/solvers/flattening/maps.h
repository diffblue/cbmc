/*******************************************************************\

Module: Map Theory (base class for array theory)

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Map Theory — base class for arrayst, providing map-theoretic
/// reasoning (key tracking, equality tracking, Ackermann constraints).

#ifndef CPROVER_SOLVERS_FLATTENING_MAPS_H
#define CPROVER_SOLVERS_FLATTENING_MAPS_H

#include <util/union_find.h>

#include "equality.h"

#include <list>
#include <map>
#include <set>

class equal_exprt;
class index_exprt;
class symbol_exprt;

/// Base class for map-theoretic reasoning (key tracking, equality tracking,
/// Ackermann constraints, constraint counting).  Subclassed by \ref arrayst,
/// which adds array-specific encoding (with/if/of/comprehension constraints).
///
/// Inheritance chain: arrayst → mapst → equalityt → prop_conv_solvert
class mapst : public equalityt
{
public:
  /// \param _ns: namespace for type lookups
  /// \param _prop: propositional solver backend
  /// \param _message_handler: message handler for logging
  /// \param _collect_constraint_stats: when true, collect and display
  ///   constraint statistics after eager conversion
  mapst(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &_message_handler,
    bool _collect_constraint_stats = false);

  ~mapst() override = default;

  /// Record that two map expressions are equal and return a literal
  /// representing that equality.  Implemented by \ref arrayst.
  virtual literalt record_equality(const equal_exprt &expr) = 0;

  /// Record that \p s is a let-bound alias for \p v.  For map-typed bindings
  /// this connects the two expressions in the union-find so that element-wise
  /// constraints propagate correctly.  Implemented by \ref arrayst.
  virtual void record_let_binding(const symbol_exprt &s, const exprt &v) = 0;

  /// Register a key expression (an index into a map) so that the map theory
  /// generates the appropriate read-over-write and Ackermann constraints for
  /// it.  The key is recorded against the map's equivalence-class
  /// representative in \ref domain_map.
  void record_key(const index_exprt &expr);

protected:
  const namespacet &ns;
  messaget log;

  /// Tracks an equality between two map expressions together with the
  /// propositional literal that represents it.
  struct map_equalityt
  {
    literalt l;
    exprt f1, f2;
  };
  typedef std::list<map_equalityt> map_equalitiest;
  /// All recorded map equalities.  Uses a list so that references remain
  /// stable as new equalities are added.
  map_equalitiest map_equalities;

  /// Union-find grouping map expressions into equivalence classes.
  union_find<exprt, irep_hash> maps;

  typedef std::set<exprt> key_sett;
  typedef std::map<std::size_t, key_sett> domain_mapt;
  /// Maps each equivalence-class number to the set of keys (index
  /// expressions) that have been observed for that class.
  domain_mapt domain_map;
  /// Equivalence-class numbers whose key sets have been modified since the
  /// last call to \ref update_domain_map.
  std::set<std::size_t> dirty_classes;

  /// Recursively traverse a map expression \p a, unifying it with its
  /// sub-maps in the union-find and recording any keys that appear.
  /// \param a: a map-typed expression (with, if, update, typecast, …)
  void collect_maps(const exprt &a);

  /// Merge key sets of non-root equivalence classes into their roots.
  /// When \p update_all is true every class is processed; otherwise only
  /// the classes listed in \ref dirty_classes are processed.
  /// \param update_all: if true, process all classes; otherwise only dirty ones
  void update_domain_map(bool update_all);

  /// Merge the key set of equivalence class \p i into its root's key set.
  /// \param i: equivalence-class number to merge
  void update_domain_map(std::size_t i);

  /// Classification of lazily deferred constraints.
  enum class lazy_typet
  {
    MAP_ACKERMANN,
    MAP_WITH,
    MAP_IF,
    MAP_OF,
    MAP_TYPECAST,
    MAP_CONSTANT,
    MAP_COMPREHENSION,
    MAP_LET
  };

  /// A constraint together with its classification, used for lazy dispatch.
  struct lazy_constraintt
  {
    lazy_typet type;
    exprt lazy;

    lazy_constraintt(lazy_typet _type, const exprt &_lazy)
      : type(_type), lazy(_lazy)
    {
    }
  };

  /// Constraints that have been deferred for later refinement.
  std::list<lazy_constraintt> lazy_constraints;
  /// When true, constraints passed to \ref add_map_constraint with
  /// refine=true are deferred rather than added eagerly.
  bool defer_constraints;
  /// When true, constraint statistics are collected and displayed after
  /// eager conversion.
  bool collect_constraint_stats;

  /// Add a map-theory constraint.  When \ref defer_constraints is true and
  /// \p refine is true the constraint is deferred; otherwise it is
  /// converted and asserted immediately.
  /// \param lazy: the constraint to add
  /// \param refine: if true and lazy mode is active, defer the constraint
  void add_map_constraint(const lazy_constraintt &lazy, bool refine = true);

  /// Add Ackermann constraints for every pair of keys in each equivalence
  /// class: if two keys are equal then the corresponding map lookups must
  /// yield equal values.  Complexity is quadratic in the size of each key
  /// set.
  void add_Ackermann_constraints();

  /// For a recorded map equality f1 = f2, add element-wise constraints
  /// f1[k] = f2[k] for every key k in \p key_set.
  /// \param key_set: the set of keys to instantiate
  /// \param equality: the map equality whose literal guards the constraints
  void add_map_equality_constraints(
    const key_sett &key_set,
    const map_equalityt &equality);

  /// Classification of constraints for statistics reporting.
  enum class constraint_typet
  {
    MAP_ACKERMANN,
    MAP_WITH,
    MAP_IF,
    MAP_OF,
    MAP_TYPECAST,
    MAP_CONSTANT,
    MAP_COMPREHENSION,
    MAP_EQUALITY,
    MAP_LET
  };
  typedef std::map<constraint_typet, size_t> map_constraint_countt;
  /// Per-type constraint counts, populated when \ref collect_constraint_stats
  /// is true.
  map_constraint_countt constraint_count;

  /// Return a human-readable string for a constraint type enum value.
  std::string enum_to_string(constraint_typet type);

  /// Emit the collected constraint counts as a JSON object to the status log.
  void display_constraint_count();

  /// Finish eager conversion: first convert maps, then equalities, then
  /// optionally display constraint statistics.
  void finish_eager_conversion() override
  {
    finish_eager_conversion_maps();
    equalityt::finish_eager_conversion();
    if(collect_constraint_stats)
      display_constraint_count();
  }

  /// Collect all keys, build the initial domain map, and add any
  /// theory-specific constraints. The default of "collect_keys then
  /// update_domain_map" cannot live here anymore because key collection is
  /// theory-specific (e.g. \ref arrayst skips bounded-array operands), so
  /// derived classes are required to provide their own implementation.
  virtual void finish_eager_conversion_maps() = 0;
};

#endif // CPROVER_SOLVERS_FLATTENING_MAPS_H
