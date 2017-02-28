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
#include <util/replace_expr.h>
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
  string_refinementt(
    const namespacet &_ns,
    propt &_prop,
    unsigned refinement_bound);

  void set_mode();

  // Should we use counter examples at each iteration?
  bool use_counter_example;

  bool do_concretizing;

  virtual std::string decision_procedure_text() const override
  {
    return "string refinement loop with "+prop.solver_text();
  }

  static exprt is_positive(const exprt &x);

  exprt get(const exprt &expr) const override;

protected:
  typedef std::set<exprt> expr_sett;
  typedef std::list<exprt> exprt_listt;

  decision_proceduret::resultt dec_solve() override;

  bvt convert_bool_bv(const exprt &boole, const exprt &orig);

private:
  // Base class
  typedef bv_refinementt supert;

  unsigned initial_loop_bound;

  // Is the current model correct
  bool concrete_model;

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
  replace_mapt symbol_resolve;
  std::map<exprt, exprt_listt> reverse_symbol_resolve;
  std::list<std::pair<exprt, bool>> non_string_axioms;

  // Valuation in the current model of the symbols that have been created
  // by the solver
  replace_mapt current_model;

  void add_equivalence(const irep_idt & lhs, const exprt & rhs);

  void display_index_set();

  void add_lemma(const exprt &lemma,
                 bool simplify=true,
                 bool add_to_index_set=true);

  exprt substitute_function_applications(exprt expr);
  typet substitute_java_string_types(typet type);
  exprt substitute_java_strings(exprt expr);
  void add_symbol_to_symbol_map(const exprt &lhs, const exprt &rhs);
  bool is_char_array(const typet &type) const;
  bool add_axioms_for_string_assigns(const exprt &lhs, const exprt &rhs);
  void set_to(const exprt &expr, bool value) override;

  void add_instantiations();
  void add_negation_of_constraint_to_solver(
    const string_constraintt &axiom, supert &solver);
  void fill_model();
  bool check_axioms();

  void set_char_array_equality(const exprt &lhs, const exprt &rhs);
  void update_index_set(const exprt &formula);
  void update_index_set(const std::vector<exprt> &cur);
  void initial_index_set(const string_constraintt &axiom);
  void initial_index_set(const std::vector<string_constraintt> &string_axioms);
  void add_to_index_set(const exprt &s, exprt i);

  exprt instantiate(
    const string_constraintt &axiom, const exprt &str, const exprt &val);

  void instantiate_not_contains(
    const string_not_contains_constraintt &axiom,
    std::list<exprt> &new_lemmas);

  exprt substitute_array_lists(exprt) const;

  exprt compute_inverse_function(
    const exprt &qvar, const exprt &val, const exprt &f);

  std::map<exprt, int> map_representation_of_sum(const exprt &f) const;
  exprt sum_over_map(
    std::map<exprt, int> &m, const typet &type, bool negated=false) const;

  exprt simplify_sum(const exprt &f) const;

  void concretize_results();
  void concretize_lengths();
  // Length of char arrays found during concretization
  std::map<exprt, exprt> found_length;

  exprt get_array(const exprt &arr, const exprt &size) const;
  exprt get_array(const exprt &arr) const;

  std::string string_of_array(const array_exprt &arr);
};

#endif
