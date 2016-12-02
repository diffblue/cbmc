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

  symbol_exprt fresh_index(const irep_idt &prefix);
  symbol_exprt fresh_boolean(const irep_idt &prefix);

  static exprt is_positive(const exprt & x);

private:  
  typedef bv_refinementt SUB;

protected:

  typedef std::set<exprt> expr_sett;
  typedef std::map<exprt, exprt> expr_mapt;
  
  virtual void post_process();
  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_function_application(
    const function_application_exprt &expr);
  virtual bvt convert_pointer_type(const exprt &expr);

  decision_proceduret::resultt dec_solve();

  // fills as many 0 as necessary in the bit vectors to have the right width
  bvt convert_bool_bv(const exprt &boole, const exprt &orig);

  // The following functions convert different string functions 
  // and add the corresponding lemmas to a list of properties to be checked  
  exprt convert_string_equal(const function_application_exprt &f);
  exprt convert_string_equals_ignore_case(const function_application_exprt &f);
  exprt convert_string_is_empty(const function_application_exprt &f);
  bvt convert_string_length(const function_application_exprt &f);
  exprt convert_string_is_prefix(const string_exprt &prefix, const string_exprt &str, const exprt & offset);
  exprt convert_string_is_prefix(const function_application_exprt &f, bool swap_arguments=false);
  bvt convert_string_is_suffix(const function_application_exprt &f, bool swap_arguments=false);
  bvt convert_string_contains(const function_application_exprt &f);
  exprt convert_string_hash_code(const function_application_exprt &f);
  exprt convert_string_index_of(const string_exprt &str, const exprt & c, const exprt & from_index);
  exprt convert_string_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index);
  exprt convert_string_last_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index);
  exprt convert_string_index_of(const function_application_exprt &f);
  exprt convert_string_last_index_of(const string_exprt &str, const exprt & c, const exprt & from_index);
  exprt convert_string_last_index_of(const function_application_exprt &f);
  bvt convert_char_literal(const function_application_exprt &f);
  bvt convert_string_char_at(const function_application_exprt &f);
  exprt convert_string_code_point_at(const function_application_exprt &f);
  exprt convert_string_code_point_before(const function_application_exprt &f);
  
  // Warning: this function is underspecified
  exprt convert_string_code_point_count(const function_application_exprt &f);
  // Warning: this function is underspecified
  exprt convert_string_offset_by_code_point(const function_application_exprt &f);
  exprt convert_string_parse_int(const function_application_exprt &f);
  exprt convert_string_to_char_array(const function_application_exprt &f);

  exprt convert_string_compare_to(const function_application_exprt &f);

  // Warning: this does not work at the moment because of the way we treat string pointers
  symbol_exprt convert_string_intern(const function_application_exprt &f);


private:

  // Tells if a char value is in the high-surrogates or low surrogates ranges
  exprt is_high_surrogate(const exprt & chr);
  exprt is_low_surrogate(const exprt & chr);

  // All constraints produced by the code
  axiom_vect string_axioms;

  // Simple constraints that have been given to the solver
  expr_sett seen_instances;
  // 
  axiom_vect universal_axioms;
  //
  axiom_vect not_contains_axioms;

  int nb_sat_iteration;

  // Boolean symbols that are used to know whether the results 
  // of some functions should be true.
  std::vector<symbol_exprt> boolean_symbols;

  // Symbols used in existential quantifications
  std::vector<symbol_exprt> index_symbols;


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

  std::map<irep_idt, string_exprt> symbol_to_string;
  inline void assign_to_symbol(const symbol_exprt & sym, const string_exprt & expr){
    symbol_to_string[sym.get_identifier()]= expr;
  }  

  string_exprt string_of_symbol(const symbol_exprt & sym);


  std::map<string_exprt, symbol_exprt> pool;
  std::map<string_exprt, symbol_exprt> hash;

  // Create a new string expression and add the necessary lemma
  // to ensure its equal to the given string expression.
  string_exprt make_string(const exprt &str);

  // Same thing but associates the string to the given symbol instead 
  // of returning it.
  void make_string(const symbol_exprt & sym, const exprt &str);

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
  void initial_index_set(const axiom_vect &string_axioms);

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
