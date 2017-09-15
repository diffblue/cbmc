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
  {
    return "string refinement loop with "+prop.solver_text();
  }

  exprt get(const exprt &expr) const override;

protected:
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

  void add_equivalence(const irep_idt & lhs, const exprt & rhs);

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

  std::vector<exprt> instantiate_not_contains(
    const string_not_contains_constraintt &axiom);

  exprt compute_inverse_function(
    const exprt &qvar, const exprt &val, const exprt &f);

  std::map<exprt, int> map_representation_of_sum(const exprt &f) const;

  bool is_valid_string_constraint(const string_constraintt &expr);

  void concretize_string(const exprt &expr);
  void concretize_results();
  void concretize_lengths();

  exprt get_array(const exprt &arr, const exprt &size) const;
  exprt get_array(const exprt &arr) const;

  std::string string_of_array(const array_exprt &arr);
};

exprt substitute_array_lists(exprt expr, size_t string_max_length);

exprt concretize_arrays_in_expression(
  exprt expr, std::size_t string_max_length);

/// Convert index-value map to a vector of values. If a value for an
/// index is not defined, set it to the value referenced by the next higher
/// index. The length of the resulting vector is the key of the map's
/// last element + 1
/// \param index_value: map containing values of specific vector cells
/// \return Vector containing values as described in the map
template <typename T>
std::vector<T> fill_in_map_as_vector(
  const std::map<std::size_t, T> &index_value)
{
  std::vector<T> result;
  if(!index_value.empty())
  {
    result.resize(index_value.rbegin()->first+1);
    for(auto it=index_value.rbegin(); it!=index_value.rend(); ++it)
    {
      const std::size_t index=it->first;
      const T value=it->second;
      const auto next=std::next(it);
      const std::size_t leftmost_index_to_pad=
        next!=index_value.rend()
        ? next->first+1
        : 0;
      for(std::size_t j=leftmost_index_to_pad; j<=index; j++)
        result[j]=value;
    }
  }
  return result;
}
#endif
