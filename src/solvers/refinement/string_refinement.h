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
#include <solvers/refinement/string_refinement_util.h>

#define DEFAULT_MAX_NB_REFINEMENT std::numeric_limits<size_t>::max()
#define CHARACTER_FOR_UNKNOWN '?'
// Limit the size of strings in traces to 64M chars to avoid memout
#define MAX_CONCRETE_STRING_SIZE (1 << 26)

class string_refinementt final: public bv_refinementt
{
private:
  struct configt
  {
    std::size_t refinement_bound=0;
    /// Concretize strings after solver is finished
    bool trace=false;
    bool use_counter_example=true;
    std::size_t max_string_length;
  };
public:
  /// string_refinementt constructor arguments
  struct infot : public bv_refinementt::infot,
                 public configt
  {
  };

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
  std::size_t max_string_length;
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

  string_dependenciest dependencies;

  void add_lemma(const exprt &lemma, bool simplify_lemma = true);
};

exprt substitute_array_lists(exprt expr, std::size_t string_max_length);

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
