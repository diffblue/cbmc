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
#include <set>
#include <unordered_set>

class equal_exprt;
class index_exprt;
class symbol_exprt;

class mapst : public equalityt
{
public:
  mapst(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &_message_handler,
    bool _get_constraints = false);

  ~mapst() override = default;

  // -- Pure virtual: implemented by arrayst --
  virtual literalt record_equality(const equal_exprt &expr) = 0;
  virtual void record_let_binding(const symbol_exprt &s, const exprt &v) = 0;

  // -- Virtual: default in mapst, may be overridden --
  virtual void record_key(const index_exprt &expr);

protected:
  const namespacet &ns;
  messaget log;

  // -- Map equality tracking --
  struct map_equalityt
  {
    literalt l;
    exprt f1, f2;
  };
  typedef std::list<map_equalityt> map_equalitiest;
  map_equalitiest map_equalities;

  // -- Maps union-find --
  union_find<exprt, irep_hash> maps;

  // -- Key tracking --
  typedef std::set<exprt> key_sett;
  typedef std::map<std::size_t, key_sett> domain_mapt;
  domain_mapt domain_map;
  std::set<std::size_t> update_keys;
  std::unordered_set<irep_idt> array_comprehension_args;

  void collect_keys();
  void collect_keys(const exprt &a);
  virtual void collect_maps(const exprt &a);
  void update_domain_map(bool update_all);
  void update_domain_map(std::size_t i);

  virtual bool is_unbounded_map(const typet &type) const = 0;

  // -- Lazy constraint management --
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

  struct lazy_constraintt
  {
    lazy_typet type;
    exprt lazy;

    lazy_constraintt(lazy_typet _type, const exprt &_lazy)
      : type(_type), lazy(_lazy)
    {
    }
  };

  std::list<lazy_constraintt> lazy_constraints;
  bool lazy_dispatch;
  bool incremental_cache;
  bool get_constraints;
  std::map<exprt, bool> expr_map;

  void add_map_constraint(const lazy_constraintt &lazy, bool refine = true);

  // -- Ackermann constraints --
  void add_Ackermann_constraints();
  void add_map_equality_constraints(
    const key_sett &key_set,
    const map_equalityt &equality);

  // -- Constraint counting --
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
  map_constraint_countt constraint_count;
  std::string enum_to_string(constraint_typet type);
  void display_constraint_count();

  // -- Eager conversion --
  void finish_eager_conversion() override
  {
    finish_eager_conversion_maps();
    equalityt::finish_eager_conversion();
    if(get_constraints)
      display_constraint_count();
  }

  virtual void finish_eager_conversion_maps()
  {
    collect_keys();
    update_domain_map(true);
  }
};

#endif // CPROVER_SOLVERS_FLATTENING_MAPS_H
