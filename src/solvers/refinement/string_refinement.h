/*******************************************************************\

Module: String support via creating string constraints and progressively
        instantiating the universal constraints as needed.
	The procedure is described in the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

/// \file
///  String support via creating string constraints and progressively
///   instantiating the universal constraints as needed. The procedure is
///   described in the PASS paper at HVC'13: "PASS: String Solving with
///   Parameterized Array and Interval Automaton" by Guodong Li and Indradeep
///   Ghosh

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H

#include <util/string_expr.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>

// Defines a limit on the string witnesses we will output.
// Longer strings are still concidered possible by the solver but
// it will not output them.
#define MAX_CONCRETE_STRING_SIZE 500

#define MAX_NB_REFINEMENT 100

class string_refinementt: public bv_refinementt
{
public:
  // refinement_bound is a bound on the number of refinement allowed
  string_refinementt(
    const namespacet &_ns, propt &_prop, unsigned refinement_bound);

  void set_mode();

  // Should we use counter examples at each iteration?
  bool use_counter_example;

  virtual std::string decision_procedure_text() const
  {
    return "string refinement loop with "+prop.solver_text();
  }

  static exprt is_positive(const exprt &x);

protected:
  typedef std::set<exprt> expr_sett;

  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_function_application(
    const function_application_exprt &expr);

  decision_proceduret::resultt dec_solve();

  bvt convert_bool_bv(const exprt &boole, const exprt &orig);

private:
  // Base class
  typedef bv_refinementt supert;

  unsigned initial_loop_bound;

  string_constraint_generatort generator;

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

  void display_index_set();

  void add_lemma(const exprt &lemma, bool add_to_index_set=true);

  bool boolbv_set_equality_to_true(const equal_exprt &expr);

  literalt convert_rest(const exprt &expr);

  void add_instantiations();

  bool check_axioms();

  void update_index_set(const exprt &formula);
  void update_index_set(const std::vector<exprt> &cur);
  void initial_index_set(const string_constraintt &axiom);
  void initial_index_set(const std::vector<string_constraintt> &string_axioms);

  exprt instantiate(
    const string_constraintt &axiom, const exprt &str, const exprt &val);

  void instantiate_not_contains(
    const string_not_contains_constraintt &axiom,
    std::list<exprt> &new_lemmas);

  exprt compute_inverse_function(
    const exprt &qvar, const exprt &val, const exprt &f);

  std::map<exprt, int> map_representation_of_sum(const exprt &f) const;
  exprt sum_over_map(std::map<exprt, int> &m, bool negated=false) const;

  exprt simplify_sum(const exprt &f) const;

  exprt get_array(const exprt &arr, const exprt &size);

  std::string string_of_array(const exprt &arr, const exprt &size) const;
};

#endif
