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

  virtual decision_proceduret::resultt dec_solve();

  virtual std::string decision_procedure_text() const
  { return "string refinement loop with "+prop.solver_text(); }
  
  typedef bv_refinementt SUB;

protected:
  struct string_axiomt
  {
  public:
    explicit string_axiomt(unsigned i=0): id_nr(i) {}
    
    unsigned id_nr;
    literalt lit;
    exprt idx;
    exprt premise;
    exprt body;

    std::string as_string() const;
  };
  
  virtual void convert_symbol(const exprt &expr, bvt &bv);
  virtual void convert_struct(const struct_exprt &expr, bvt &bv);
  virtual void convert_function_application(
    const function_application_exprt &expr, bvt &bv);
  virtual void set_to(const exprt &expr, bool value);
  virtual void check_SAT();

  bool is_string_type(const typet &type);
  bool is_char_type(const typet &type);
  
  void convert_string_equal(const function_application_exprt &f, bvt &bv);
  void convert_string_length(const function_application_exprt &f, bvt &bv);
  void convert_string_concat(const function_application_exprt &f, bvt &bv);
  void convert_string_substring(const function_application_exprt &f, bvt &bv);
  void convert_string_is_prefix(const function_application_exprt &f, bvt &bv);
  void convert_string_is_suffix(const function_application_exprt &f, bvt &bv);
  void convert_string_literal(const function_application_exprt &f, bvt &bv);
  void convert_char_literal(const function_application_exprt &f, bvt &bv);
  void convert_string_char_at(const function_application_exprt &f, bvt &bv);
  void convert_string_char_set(const function_application_exprt &f, bvt &bv);

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

  std::vector<string_axiomt> string_axioms;
};

#endif
