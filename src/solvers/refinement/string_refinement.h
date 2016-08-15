/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_REFINEMENT_H
#define CPROVER_SOLVER_STRING_REFINEMENT_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>

#define INDEX_WIDTH 32
#define CHAR_WIDTH 8


// Internal type used for strings
class string_ref_typet : public struct_typet {
public:
  string_ref_typet();

  // Type for the content (list of characters) of a string
  inline array_typet get_content_type() 
  { return to_array_type((to_struct_type(*this)).components()[1].type());}

};


class string_axiomt
{
public:
  // Universally quantified symbol
  symbol_exprt qvar;
  exprt premise;
  exprt body;

  // Axiom of the form: forall index. prem ==> bod
  string_axiomt(symbol_exprt index, exprt prem, exprt bod);

  // Axiom with no quantification
  string_axiomt(exprt bod);

  inline bool is_quantified() {return (premise != true_exprt());}
};

typedef std::vector<string_axiomt> axiom_vect;

// Expressions that encode strings
class string_exprt : public struct_exprt {
public:
  string_exprt();

  // Add to the list of axioms, lemmas which should hold for the string to be 
  // equal to the given expression.
  static string_exprt of_expr(const exprt & unrefined_string, axiom_vect & axioms);

  // Find the string corresponding to the given symbol if it exists.
  // Otherwise a new string is created.
  static string_exprt find_symbol(const symbol_exprt &expr);

  // Expression corresponding to the length of the string
  inline const exprt & length() const { return op0();};
  // Expression corresponding to the content (array of characters) of the string
  inline const exprt & content() const { return op1();};

  // Expression of the character at position idx in the string
  inline index_exprt operator[] (exprt idx)
  { return index_exprt(content(), idx);}

  // Comparison on the length of the strings
  inline binary_relation_exprt operator< (string_exprt rhs)
  { return binary_relation_exprt(length(), ID_lt, rhs.length()); }
  inline binary_relation_exprt operator> (string_exprt rhs)
  { return binary_relation_exprt(rhs.length(), ID_lt, length()); }
  inline binary_relation_exprt operator<= (string_exprt rhs)
  { return binary_relation_exprt(length(), ID_le, rhs.length()); }
  inline binary_relation_exprt operator>= (string_exprt rhs)
  { return binary_relation_exprt(length(), ID_ge, rhs.length()); }
  inline binary_relation_exprt operator< (const symbol_exprt & rhs)
  { return binary_relation_exprt(length(), ID_lt, rhs); }
  inline binary_relation_exprt operator> (const symbol_exprt & rhs)
  { return binary_relation_exprt(rhs, ID_lt, length()); }

private:
  // Auxiliary functions for of_expr
  void of_function_application(const function_application_exprt &expr, axiom_vect & axioms);

  void of_string_literal(const function_application_exprt &f,axiom_vect &axioms);
  void of_string_concat(const function_application_exprt &f,axiom_vect &axioms);
  void of_string_substring(const function_application_exprt &expr,axiom_vect &axioms);
  void of_string_char_set(const function_application_exprt &expr,axiom_vect &axioms);
  
  friend inline string_exprt &to_string_expr(exprt &expr)
  {
    assert(expr.id()==ID_struct);
    return static_cast<string_exprt &>(expr);
  }
  
};

string_exprt &to_string_expr(exprt expr);


class string_refinementt: public bv_refinementt
{
public:
  string_refinementt(const namespacet &_ns, propt &_prop);
  ~string_refinementt();

  virtual std::string decision_procedure_text() const
  { return "string refinement loop with "+prop.solver_text(); }

  static bool is_unrefined_string_type(const typet &type);
  static bool is_unrefined_char_type(const typet &type);
  
  // Generate a new symbol of the given type tp with a prefix 
  static symbol_exprt fresh_symbol(const irep_idt &prefix,
				   const typet &tp=bool_typet());


  inline std::string axiom_to_string(const string_axiomt & ax) {
    return ("forall " + pretty_short(ax.qvar) + ". (" 
	    + pretty_short(ax.premise) + ") ==> " + pretty_short(ax.body));
  }


  irep_idt string_literal_func;
  irep_idt char_literal_func;
  irep_idt string_length_func;
  irep_idt string_equal_func;
  irep_idt string_copy_func;
  irep_idt string_char_at_func;
  irep_idt string_concat_func;
  irep_idt string_substring_func;
  irep_idt string_is_prefix_func;
  irep_idt string_is_suffix_func;
  irep_idt string_char_set_func;

private:  
  typedef bv_refinementt SUB;

  string_ref_typet string_type;

  inline size_t get_string_width()
  { return boolbv_width(string_type);}

  static unsigned next_symbol_id;

protected:

  typedef std::set<exprt> expr_sett;
  typedef std::map<exprt, exprt> expr_mapt;
  
  virtual void post_process();
  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_function_application(
    const function_application_exprt &expr);
  virtual void check_SAT();

  // fills as many 0 as necessary in the bit vectors to have the right width
  bvt convert_bool_bv(const exprt &boole, const exprt &orig);

  // The following functions convert different string functions to 
  // bit vectors and add the corresponding lemmas to a list of
  // properties to be checked  
  bvt convert_string_equal(const function_application_exprt &f);
  bvt convert_string_copy(const function_application_exprt &f);
  bvt convert_string_length(const function_application_exprt &f);
  bvt convert_string_is_prefix(const function_application_exprt &f);
  bvt convert_string_is_suffix(const function_application_exprt &f);
  bvt convert_char_literal(const function_application_exprt &f);
  bvt convert_string_char_at(const function_application_exprt &f);

private:
  // Boolean symbols that are used to know whether the results 
  // of some functions should be true.
  std::vector<symbol_exprt> boolean_symbols;
  axiom_vect string_axioms;

  // Create a new string expression and add the necessary lemma
  // to ensure its equal to the given string expression.
  string_exprt make_string(const exprt &str);

  // Same thing but associates the string to the given symbol instead 
  // of returning it.
  void make_string(const symbol_exprt & sym, const exprt &str);

  //void set_to(const exprt &expr, bool value);
  bool boolbv_set_equality_to_true(const equal_exprt &expr);
  //bool set_equality_to_true(const equal_exprt &expr);
  literalt convert_rest(const exprt &expr);

  void add_lemma(const exprt &lemma);
  void add_lemmas(axiom_vect & lemmas);

  void add_instantiations(bool first=false);
  bool check_axioms();

  // See the definition in the PASS article
  // this is indexed by array_expressions
  std::map<exprt, expr_sett> index_set;

  // Add to the index set all the indices that appear in the formula
  void update_index_set(const exprt &formula);
  void update_index_set(const string_axiomt &axiom);

  // Takes an universaly quantified formula [axiom], 
  // an array of char variable [s], and an index expression [val]. 
  // Computes one index [v1] in which [axiom.idx] appears, takes the
  // corresponding substitition [r] (obtained with [compute_subst]).
  // Then substitutes [axiom.idx] with [r] in [axiom].
  exprt instantiate(const string_axiomt &axiom, const exprt &str,
                    const exprt &val);

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

  // Gets a model of an array and put it in a certain form
  exprt get_array(const exprt &arr, const exprt &size);

  // Convert the content of a string to a more readable representation
  std::string string_of_array(const exprt &arr, const exprt &size);

  // Lemmas that were already added
  expr_sett seen_instances;

  // current set of lemmas (unquantified)
  std::vector<exprt> cur;

  // succinct and pretty way to display an expression
  std::string pretty_short(const exprt & expr);

};

#endif
