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
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <solvers/refinement/string_refinement_invariant.h>

#define MAX_NB_REFINEMENT 100

class string_refinementt final: public bv_refinementt
{
private:
  struct configt {
    unsigned refinement_bound=0;
    /// Make non-deterministic character arrays have at least one character
    bool string_non_empty=false;
    /// Concretize strings after solver is finished
    bool trace=false;
    bool use_counter_example=false;
  };
public:
  /// string_refinementt constructor arguments
  struct infot:
    public bv_refinementt::infot,
    public string_constraint_generatort::infot,
    public configt { };

  explicit string_refinementt(const infot &);

  virtual std::string decision_procedure_text() const override
  { return "string refinement loop with "+prop.solver_text(); }

  exprt get(const exprt &expr) const override;
  void set_to(const exprt &expr, bool value) override;
  decision_proceduret::resultt dec_solve() override;

private:
  // Base class
  typedef bv_refinementt supert;

  typedef std::set<exprt> expr_sett;
  typedef std::list<exprt> exprt_listt;

  string_refinementt(const infot &, bool);
  bvt convert_bool_bv(const exprt &boole, const exprt &orig);

  const configt config_;
  unsigned loop_bound_;
  string_constraint_generatort generator;
  expr_sett nondet_arrays;

  // Simple constraints that have been given to the solver
  expr_sett seen_instances;

  std::vector<string_constraintt> universal_axioms;

  std::vector<string_not_contains_constraintt> not_contains_axioms;

  // Unquantified lemmas that have newly been added
  std::vector<exprt> cur;

  // See the definition in the PASS article
  // Warning: this is indexed by array_expressions and not string expressions
  std::map<exprt, expr_sett> current_index_set;
  std::map<exprt, expr_sett> index_set;
  replace_mapt symbol_resolve;
  std::map<exprt, exprt_listt> reverse_symbol_resolve;
  std::list<std::pair<exprt, bool>> non_string_axioms;

  // Length of char arrays found during concretization
  std::map<exprt, exprt> found_length;
  // Content of char arrays found during concretization
  std::map<exprt, array_exprt> found_content;

  void add_lemma(const exprt &lemma,
                 bool simplify=true,
                 bool add_to_index_set=true);

  bool add_axioms_for_string_assigns(const exprt &lhs, const exprt &rhs);

  void debug_model();

  void set_char_array_equality(const exprt &lhs, const exprt &rhs);

  std::vector<exprt> instantiate_not_contains(
    const string_not_contains_constraintt &axiom);

  exprt get_array(const exprt &arr, const exprt &size) const;
  exprt get_array(const exprt &arr) const;

  std::string string_of_array(const array_exprt &arr);
};
#endif
