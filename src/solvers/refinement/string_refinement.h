/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_REFINEMENT_H
#define CPROVER_SOLVER_STRING_REFINEMENT_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_expr.h>
#include <solvers/refinement/string_constraint_generator.h>

// This is to analyse the performances of the different steps
#include <chrono>

class string_refinementt: public bv_refinementt
{
public:
  string_refinementt(const namespacet &_ns, propt &_prop);
  ~string_refinementt() {};

  // Should we use counter examples at each iteration?
  bool use_counter_example;

  // Number of time we refine the index set before actually launching the solver
  int initial_loop_bound;

  virtual std::string decision_procedure_text() const
  { return "string refinement loop with "+prop.solver_text(); }

  static exprt is_positive(const exprt & x);

private:  
  typedef bv_refinementt SUB;
  std::chrono::high_resolution_clock::time_point start_time;


protected:

  typedef std::set<exprt> expr_sett;
  
  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_function_application
  (const function_application_exprt &expr);
  
  decision_proceduret::resultt dec_solve();

  // fills as many 0 as necessary in the bit vectors to have the right width
  bvt convert_bool_bv(const exprt &boole, const exprt &orig);


private:
  
  string_constraint_generatort generator;

  // Simple constraints that have been given to the solver
  expr_sett seen_instances;
  // 
  std::vector<string_constraintt> universal_axioms;
  //
  std::vector<string_constraintt> not_contains_axioms;

  int nb_sat_iteration;

  // Unquantified lemmas that have newly been added
  std::vector<exprt> cur;

  // See the definition in the PASS article
  // Warning: this is indexed by array_expressions and not string expressions
  std::map<exprt, expr_sett> current_index_set;
  std::map<exprt, expr_sett> index_set;

  // for debugging
  void display_index_set();

  // Tells if there is a index in the index set where the same variable occurs several time.
  bool variable_with_multiple_occurence_in_index;

  // Natural number expression corresponding to a constant integer
  constant_exprt constant_of_nat(int i,typet t);

  void add_lemma(const exprt &lemma, bool add_to_index_set=true);

  //void set_to(const exprt &expr, bool value);
  bool boolbv_set_equality_to_true(const equal_exprt &expr);
  //bool set_equality_to_true(const equal_exprt &expr);
  literalt convert_rest(const exprt &expr);

  // Instantiate forall constraints with index from the index set
  void add_instantiations();

  // Return true if the current model satisfies all the axioms
  bool check_axioms();

  // Add to the index set all the indices that appear in the formula
  void update_index_set(const exprt &formula);
  void update_index_set(const std::vector<exprt> &cur);
  void initial_index_set(const string_constraintt &axiom);
  void initial_index_set(const std::vector<string_constraintt> &string_axioms);

  // Takes an universaly quantified formula [axiom], 
  // an array of char variable [s], and an index expression [val]. 
  // Computes one index [v1] in which [axiom.idx] appears, takes the
  // corresponding substitition [r] (obtained with [compute_subst]).
  // Then substitutes [axiom.idx] with [r] in [axiom].
  // axiom is not constant because we may record some information about 
  // instantiation of existential variables.
  string_constraintt instantiate(const string_constraintt &axiom, const exprt &str,
                    const exprt &val);

  void instantiate_not_contains(const string_constraintt &axiom, std::vector<exprt> & new_lemmas);

  // For expressions f of a certain form, 		  //
  // returns an expression corresponding to $f^{−1}(val)$.//
  // i.e. the value that is necessary for qvar for f to   //
  // be equal to val.                                     //
  // Takes an expression containing + and − operations 	  //
  // in which qvar appears exactly once. 		  //
  // Rewrites it as a sum of qvar and elements in list	  //
  // elems different from qvar. 			  //
  // Takes e minus the sum of the element in elems.	  //
  exprt compute_subst(const exprt &qvar, const exprt &val, const exprt &f);
  
  // Rewrite a sum in a simple form: sum m_i * expr_i
  std::map< exprt, int> map_of_sum(const exprt &f);
  exprt sum_of_map(std::map<exprt,int> &m,bool negated=false);

  // Simplify a sum (an expression with only plus and minus expr)
  exprt simplify_sum(const exprt &f);

  // Gets a model of an array and put it in a certain form
  exprt get_array(const exprt &arr, const exprt &size);

  // Convert the content of a string to a more readable representation
  std::string string_of_array(const exprt &arr, const exprt &size);

  // succinct and pretty way to display an expression
  std::string pretty_short(const exprt & expr);

  void print_time(std::string s);
};

#endif
