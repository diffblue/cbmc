/*******************************************************************\

Module: String support via creating string constraints and progressively
        instantiating the universal constraints as needed.
        The procedure is described in the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

/// \file
/// String support via creating string constraints and progressively
///   instantiating the universal constraints as needed. The procedure is
///   described in the PASS paper at HVC'13: "PASS: String Solving with
///   Parameterized Array and Interval Automaton" by Guodong Li and Indradeep
///   Ghosh

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H

#include <limits>
#include <util/string_expr.h>
#include <util/replace_expr.h>
#include <util/union_find_replace.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <solvers/refinement/string_refinement_invariant.h>

#define DEFAULT_MAX_NB_REFINEMENT std::numeric_limits<size_t>::max()
#define CHARACTER_FOR_UNKNOWN '?'

struct index_set_pairt
{
  std::map<exprt, std::set<exprt>> cumulative;
  std::map<exprt, std::set<exprt>> current;
};

struct string_axiomst
{
  std::vector<string_constraintt> universal;
  std::vector<string_not_contains_constraintt> not_contains;
};

/// Represents arrays of the form `array_of(x) with {i:=a} with {j:=b} ...`
/// by a default value `x` and a list of entries `(i,a)`, `(j,b)` etc.
class sparse_arrayt
{
public:
  /// Initialize a sparse array from an expression of the form
  /// `array_of(x) with {i:=a} with {j:=b} ...`
  /// This is the form in which array valuations coming from the underlying
  /// solver are given.
  explicit sparse_arrayt(const with_exprt &expr);

  /// Creates an if_expr corresponding to the result of accessing the array
  /// at the given index
  virtual exprt to_if_expression(const exprt &index) const;

protected:
  exprt default_value;
  std::vector<std::pair<std::size_t, exprt>> entries;
};

/// Represents arrays by the indexes up to which the value remains the same.
/// For instance `{'a', 'a', 'a', 'b', 'b', 'c'}` would be represented by
/// by ('a', 2) ; ('b', 4), ('c', 5).
/// This is particularly useful when the array is constant on intervals.
class interval_sparse_arrayt final : public sparse_arrayt
{
public:
  /// An expression of the form `array_of(x) with {i:=a} with {j:=b}` is
  /// converted to an array `arr` where for all index `k` smaller than `i`,
  /// `arr[k]` is `a`, for all index between `i` (exclusive) and `j` it is `b`
  /// and for the others it is `x`.
  explicit interval_sparse_arrayt(const with_exprt &expr);
  exprt to_if_expression(const exprt &index) const override;
};

class string_refinementt final: public bv_refinementt
{
private:
  struct configt
  {
    std::size_t refinement_bound=0;
    /// Concretize strings after solver is finished
    bool trace=false;
    bool use_counter_example=true;
  };
public:
  /// string_refinementt constructor arguments
  struct infot:
    public bv_refinementt::infot,
    public string_constraint_generatort::infot,
    public configt { };

  explicit string_refinementt(const infot &);

  std::string decision_procedure_text() const override
  { return "string refinement loop with "+prop.solver_text(); }

  exprt get(const exprt &expr) const override;
  void set_to(const exprt &expr, bool value) override;
  decision_proceduret::resultt dec_solve() override;

private:
  // Base class
  typedef bv_refinementt supert;

  string_refinementt(const infot &, bool);

  const configt config_;
  std::size_t loop_bound_;
  string_constraint_generatort generator;

  // Simple constraints that have been given to the solver
  std::set<exprt> seen_instances;

  string_axiomst axioms;

  // Unquantified lemmas that have newly been added
  std::vector<exprt> current_constraints;

  // See the definition in the PASS article
  // Warning: this is indexed by array_expressions and not string expressions

  index_set_pairt index_sets;
  union_find_replacet symbol_resolve;

  std::vector<equal_exprt> equations;

  void add_lemma(const exprt &lemma, bool simplify_lemma = true);
};

exprt substitute_array_lists(exprt expr, std::size_t string_max_length);
exprt concretize_arrays_in_expression(
  exprt expr,
  std::size_t string_max_length,
  const namespacet &ns);

bool is_char_array_type(const typet &type, const namespacet &ns);

bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred);

// Declaration required for unit-test:
union_find_replacet string_identifiers_resolution_from_equations(
  std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream);

// Declaration required for unit-test:
exprt substitute_array_access(
  exprt expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate);

#endif
