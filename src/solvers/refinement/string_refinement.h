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

#include <util/string_expr.h>
#include <util/replace_expr.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <solvers/refinement/string_refinement_invariant.h>

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

  // Should we concretize strings when the solver finished
  bool do_concretizing;

  void set_max_string_length(size_t i);
  void enforce_non_empty_string();
  void enforce_printable_characters();

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

  string_constraint_generatort generator;

  bool non_empty_string;
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

  void add_equivalence(const irep_idt & lhs, const exprt & rhs);

  void display_index_set();

  void add_lemma(const exprt &lemma,
                 bool simplify=true,
                 bool add_to_index_set=true);

  exprt substitute_function_applications(exprt expr);
  typet substitute_java_string_types(typet type);
  exprt substitute_java_strings(exprt expr);
  exprt substitute_array_with_expr(const exprt &expr, const exprt &index) const;
  void substitute_array_access(exprt &expr) const;
  void add_symbol_to_symbol_map(const exprt &lhs, const exprt &rhs);
  bool is_char_array(const typet &type) const;
  bool add_axioms_for_string_assigns(const exprt &lhs, const exprt &rhs);
  void set_to(const exprt &expr, bool value) override;

  void add_instantiations();
  exprt negation_of_not_contains_constraint(
    const string_not_contains_constraintt &axiom,
    const exprt &val,
    const symbol_exprt &univ_var);
  exprt negation_of_constraint(const string_constraintt &axiom);
  void debug_model();
  bool check_axioms();
  bool is_axiom_sat(
    const exprt &axiom, const symbol_exprt& var, exprt &witness);

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
  template <typename T1, typename T2>
  void pad_vector(
    std::vector<T1> &result,
    std::set<T2> &initialized,
    T1 last_concretized) const;

  void concretize_string(const exprt &expr);
  void concretize_results();
  void concretize_lengths();

  exprt get_array(const exprt &arr, const exprt &size) const;
  exprt get_array(const exprt &arr) const;

  std::string string_of_array(const array_exprt &arr);
};

/// Utility function for concretization of strings. Copies concretized values to
/// the left to initialize the unconcretized indices of concrete_array.
/// \param concrete_array: the vector to populate
/// \param initialized: the vector containing the indices of the concretized
///   values
/// \param last_concretized: initial value of the last concretized index
template <typename T1, typename T2>
void string_refinementt::pad_vector(
  std::vector<T1> &concrete_array,
  std::set<T2> &initialized,
  T1 last_concretized) const
{
  // Pad the concretized values to the left to assign the uninitialized
  // values of result. The indices greater than concretize_limit are
  // already assigned to last_concretized.
  for(auto j=initialized.rbegin(); j!=initialized.rend();)
  {
    size_t i=*j;
    // The leftmost index to pad is the value + 1 of the next element in
    // 'initialized'. Since we cannot use the binary '+' operator on set
    // iterators, we must increment the iterator here instead of in the
    // for loop.
    j++;
    size_t leftmost_index_to_pad=(j!=initialized.rend()?*(j)+1:0);
    // pad until we reach the next initialized index (right to left)
    while(i>leftmost_index_to_pad)
      concrete_array[(i--)-1]=last_concretized;
    INVARIANT(
      i==leftmost_index_to_pad,
      string_refinement_invariantt("Loop decrements i until it is not greater "
        " than leftmost_index_to_pad"));
    if(i>0)
      last_concretized=concrete_array[i-1];
  }
}
#endif
