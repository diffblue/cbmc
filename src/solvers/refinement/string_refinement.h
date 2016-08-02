/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_REFINEMENT_H
#define CPROVER_SOLVER_STRING_REFINEMENT_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>

class string_refinementt: public bv_refinementt
{
public:
  string_refinementt(const namespacet &_ns, propt &_prop);
  ~string_refinementt();

  virtual std::string decision_procedure_text() const
  { return "string refinement loop with "+prop.solver_text(); }
  
  typedef bv_refinementt SUB;

protected:
  struct string_axiomt
  {
  public:
    explicit string_axiomt(unsigned i=0): id_nr(i) {}
    
    unsigned id_nr;
    exprt lit;
    exprt idx;
    exprt premise;
    exprt body;

    std::string as_string() const;
  };

  typedef std::vector<string_axiomt> axiom_vect;
  typedef std::set<exprt> expr_sett;
  typedef std::map<exprt, exprt> expr_mapt;
  typedef std::map<exprt, expr_sett> index_sett;
  
  virtual void post_process();
  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_struct(const struct_exprt &expr);
  virtual bvt convert_function_application(
    const function_application_exprt &expr);
  virtual void check_SAT();

  bool is_string_type(const typet &type);
  bool is_char_type(const typet &type);

  bvt convert_bool_bv(const exprt &boole, const exprt &orig);
  
  bvt convert_string_equal(const function_application_exprt &f);
  bvt convert_string_length(const function_application_exprt &f);
  bvt convert_string_concat(const function_application_exprt &f);
  bvt convert_string_substring(const function_application_exprt &f);
  bvt convert_string_is_prefix(const function_application_exprt &f);
  bvt convert_string_is_suffix(const function_application_exprt &f);
  bvt convert_string_literal(const function_application_exprt &f);
  bvt convert_char_literal(const function_application_exprt &f);
  bvt convert_string_char_at(const function_application_exprt &f);
  bvt convert_string_char_set(const function_application_exprt &f);

  void add_instantiations(bool first=false);
  bool check_axioms();
  void update_index_set(const exprt &formula);
  void update_index_set(const string_axiomt &axiom);
  exprt instantiate(const string_axiomt &axiom, const exprt &str,
                    const exprt &val);
  void add_lemma(const exprt &lemma);

  symbol_exprt fresh_symbol(const irep_idt &prefix,
                            const typet &tp=bool_typet());
  typet index_type();
  typet char_type();
  exprt make_array(const exprt &str);
  exprt make_length(const exprt &str);
  exprt get_array(const exprt &arr, const exprt &size);

  void expect(bool cond, const char *errmsg=NULL);

  irep_idt string_literal_func;
  irep_idt char_literal_func;
  irep_idt string_length_func;
  irep_idt string_equal_func;
  irep_idt string_char_at_func;
  irep_idt string_concat_func;
  irep_idt string_substring_func;
  irep_idt string_is_prefix_func;
  irep_idt string_is_suffix_func;
  irep_idt string_char_set_func;
  size_t string_length_width;

  axiom_vect string_axioms;
  expr_sett strings;
  expr_mapt string2length;
  expr_mapt length2string;
  expr_mapt string2array;
  expr_sett seen_instances;
  index_sett index_set;
  unsigned next_symbol_id;

  std::vector<exprt> cur;
};

#endif
