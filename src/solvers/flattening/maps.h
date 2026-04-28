/*******************************************************************\

Module: Map Theory (base class for array theory)

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Map Theory — base class for arrayst, providing map-theoretic
/// reasoning (index tracking, equality tracking, Ackermann constraints).

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
    bool _get_array_constraints = false);

  ~mapst() override = default;

  // -- Pure virtual: implemented by arrayst --
  virtual literalt record_array_equality(const equal_exprt &expr) = 0;
  virtual void
  record_array_let_binding(const symbol_exprt &s, const exprt &v) = 0;

  // -- Virtual: default in mapst, may be overridden --
  virtual void record_array_index(const index_exprt &expr);

protected:
  const namespacet &ns;
  messaget log;

  // -- Array equality tracking --
  struct array_equalityt
  {
    literalt l;
    exprt f1, f2;
  };
  typedef std::list<array_equalityt> array_equalitiest;
  array_equalitiest array_equalities;

  // -- Arrays union-find --
  union_find<exprt, irep_hash> arrays;

  // -- Index tracking --
  typedef std::set<exprt> index_sett;
  typedef std::map<std::size_t, index_sett> index_mapt;
  index_mapt index_map;
  std::set<std::size_t> update_indices;
  std::unordered_set<irep_idt> array_comprehension_args;

  void collect_indices();
  void collect_indices(const exprt &a);
  virtual void collect_arrays(const exprt &a);
  void update_index_map(bool update_all);
  void update_index_map(std::size_t i);

  virtual bool is_unbounded_array(const typet &type) const = 0;

  // -- Lazy constraint management --
  enum class lazy_typet
  {
    ARRAY_ACKERMANN,
    ARRAY_WITH,
    ARRAY_IF,
    ARRAY_OF,
    ARRAY_TYPECAST,
    ARRAY_CONSTANT,
    ARRAY_COMPREHENSION,
    ARRAY_LET
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

  std::list<lazy_constraintt> lazy_array_constraints;
  bool lazy_arrays;
  bool incremental_cache;
  bool get_array_constraints;
  std::map<exprt, bool> expr_map;

  void add_array_constraint(const lazy_constraintt &lazy, bool refine = true);

  // -- Ackermann constraints --
  void add_array_Ackermann_constraints();
  void add_array_constraints_equality(
    const index_sett &index_set,
    const array_equalityt &array_equality);

  // -- Constraint counting --
  enum class constraint_typet
  {
    ARRAY_ACKERMANN,
    ARRAY_WITH,
    ARRAY_IF,
    ARRAY_OF,
    ARRAY_TYPECAST,
    ARRAY_CONSTANT,
    ARRAY_COMPREHENSION,
    ARRAY_EQUALITY,
    ARRAY_LET
  };
  typedef std::map<constraint_typet, size_t> array_constraint_countt;
  array_constraint_countt array_constraint_count;
  std::string enum_to_string(constraint_typet type);
  void display_array_constraint_count();

  // -- Eager conversion --
  void finish_eager_conversion() override
  {
    finish_eager_conversion_arrays();
    equalityt::finish_eager_conversion();
    if(get_array_constraints)
      display_array_constraint_count();
  }

  virtual void finish_eager_conversion_arrays()
  {
    collect_indices();
    update_index_map(true);
  }
};

#endif // CPROVER_SOLVERS_FLATTENING_MAPS_H
