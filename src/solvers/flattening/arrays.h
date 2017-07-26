/*******************************************************************\

Module: Theory of Arrays with Extensionality

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Theory of Arrays with Extensionality

#ifndef CPROVER_SOLVERS_FLATTENING_ARRAYS_H
#define CPROVER_SOLVERS_FLATTENING_ARRAYS_H

#include <util/graph.h>
#include <util/numbering.h>
#include <util/std_expr.h>

#include "equality.h"

#include <list>
#include <set>
#include <unordered_set>

class array_comprehension_exprt;
class array_exprt;
class array_of_exprt;
class equal_exprt;
class if_exprt;
class index_exprt;
class with_exprt;
class update_exprt;

// #define DEBUG_ARRAYST
#ifdef DEBUG_ARRAYST
#  include <util/format_expr.h>
#endif

class arrayst:public equalityt
{
public:
  arrayst(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &message_handler,
    bool get_array_constraints = false);

  void finish_eager_conversion() override
  {
    finish_eager_conversion_arrays();
    SUB::finish_eager_conversion();
    if(get_array_constraints)
      display_array_constraint_count();
  }

  // NOLINTNEXTLINE(readability/identifiers)
  typedef equalityt SUB;

  /// Notify array theory about the equality constraint \p expr over array-typed
  /// operands.
  literalt record_array_equality(const equal_exprt &expr);
  /// Notify array theory about the index expression \p expr.
  void record_array_index(const index_exprt &expr);

protected:
  const namespacet &ns;
  messaget log;
  message_handlert &message_handler;

  virtual void finish_eager_conversion_arrays()
  {
    add_array_constraints();
  }

  /// A node of the weak equivalence graph. Each node uniquely corresponds to an
  /// array term.
  struct weg_nodet : public graph_nodet<exprt>
  {
#ifdef DEBUG_ARRAYST
    exprt array;
    std::string dot_attributes(const node_indext &i) const override
    {
      return format_to_string(array);
    }
#endif
  };

  /// The weak equivalence graph. Based on J Christ, J Hoenicke: Weakly Equivalent
  /// Arrays, FroCos 2015. Also described in D Kroening, O Strichman: Decision
  /// Procedures, Section 7.4.
  /// An edge of the weak equivalence graph is annotated with either a literal
  /// recording the equality of the nodes the edge connects, or the store
  /// operation that one of the nodes performs.
  using wegt = grapht<weg_nodet>;
  wegt weg;

  void expand_weg(wegt::node_indext index)
  {
    if(index >= weg.size())
    {
      weg.resize(index + 1);
#ifdef DEBUG_ARRAYST
      weg[index].array = arrays[index];
#endif
    }
  }

  void
  add_weg_edge(wegt::node_indext a1, wegt::node_indext a2, const exprt &cond)
  {
    // TODO -- we're not always adding a condition here it seems, it's mixed up
    // with the literal encoding the equality over arrays
    weg.edge(a1, a2) = cond;
    weg.edge(a2, a1) = cond;
  }

  /// Adds all the constraints eagerly by implementing preprocessing and
  /// Algorithms 7.4.1 and 7.4.2 of Section 7.4 of Kroening and Strichman (which
  /// describe how to instantiate Lemmas 1 and 2 of Christ and Hoenicke).
  void add_array_constraints();
  void add_array_Ackermann_constraints();
  /// Extend the weak equivalence graph with an array term \p a and return its
  /// graph node.
  wegt::node_indext collect_arrays(const exprt &a);
  /// Collect all indices of index expressions contained within \p i (which may
  /// itself be an index expression.
  void collect_indices(const exprt &i);

  // Map array terms to node indices in the weak equivalence graph.
  using array_numberingt = numberingt<exprt, irep_hash>;
  array_numberingt arrays;
  static_assert(
    std::is_same<wegt::node_indext, array_numberingt::number_type>::value,
    "node index type and numbering type must match");

  // this tracks the array indices for each array
  typedef std::set<exprt> index_sett;
  using index_mapt = std::map<wegt::node_indext, index_sett>;
  index_mapt index_map;

  // path search
  struct stack_entryt
  {
    wegt::node_indext n;
    optionalt<wegt::edgest::const_iterator> edge;
    std::set<wegt::node_indext> path_nodes;
    explicit stack_entryt(
      wegt::node_indext _n,
      const std::set<wegt::node_indext> &_path_nodes)
      : n(_n), path_nodes(_path_nodes)
    {
      path_nodes.insert(n);
    }
  };
  using weg_patht = std::vector<stack_entryt>;
  void process_weg_path(const weg_patht &);

  void weg_path_condition(
    const weg_patht &,
    const exprt &index_a,
    exprt::operandst &cond) const;

  //bool incremental_cache;

  virtual bool is_unbounded_array(const typet &type) const = 0;
  // (maybe this function should be partially moved here from boolbv)

  bool get_array_constraints;
  enum class constraint_typet
  {
    ARRAY_ACKERMANN,
    ARRAY_WITH,
    ARRAY_IF,
    ARRAY_OF,
    ARRAY_TYPECAST,
    ARRAY_CONSTANT,
    ARRAY_COMPREHENSION,
    ARRAY_EQUALITY
  };

  typedef std::map<constraint_typet, size_t> array_constraint_countt;
  array_constraint_countt array_constraint_count;
  void display_array_constraint_count();
  std::string enum_to_string(constraint_typet);

  std::unordered_set<irep_idt> array_comprehension_args;
};

#endif // CPROVER_SOLVERS_FLATTENING_ARRAYS_H
