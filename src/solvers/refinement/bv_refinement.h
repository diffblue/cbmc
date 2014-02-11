/*******************************************************************\

Module: Abstraction Refinement Loop

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_BV_REFINEMENT_H
#define CPROVER_SOLVER_BV_REFINEMENT_H

#include <langapi/language_ui.h>

#include <solvers/flattening/bv_pointers.h>

#define MAX_STATE 10000

class bv_refinementt:public bv_pointerst
{
public:
  bv_refinementt(const namespacet &_ns, propt &_prop);
  ~bv_refinementt();

  virtual decision_proceduret::resultt dec_solve();

  virtual std::string decision_procedure_text() const
  { return "refinement loop with "+prop.solver_text(); }
  
  typedef bv_pointerst SUB;

  // maximal number of times we refine a formula node
  unsigned max_node_refinement;
  
  using bv_pointerst::is_in_conflict;

  void set_ui(language_uit::uit _ui) { ui=_ui; }

protected:
  resultt prop_solve();

  // the list of operator approximations
  struct approximationt
  {
  public:
    explicit approximationt(unsigned _id_nr):id_nr(_id_nr)
    {
    }
  
    exprt expr;
    unsigned no_operands;

    bvt op0_bv, op1_bv, op2_bv, result_bv;
    mp_integer op0_value, op1_value, op2_value, result_value;

    bvt under_assumptions;
    bvt over_assumptions;

    // the kind of under- or over-approximation    
    unsigned under_state, over_state;
    
    approximationt():under_state(0), over_state(0)
    {
    }
    
    std::string as_string() const;
    
    void add_over_assumption(literalt l);
    void add_under_assumption(literalt l);
    
    unsigned id_nr;
  };
  
  typedef std::list<approximationt> approximationst;
  approximationst approximations;
  
  approximationt &add_approximation(const exprt &expr, bvt &bv);
  void check_SAT(approximationt &approximation);
  void check_UNSAT(approximationt &approximation);
  void initialize(approximationt &approximation);
  void get_values(approximationt &approximation);
  bool is_in_conflict(approximationt &approximation);
  
  void check_SAT();
  void check_UNSAT();
  bool progress;
  
  // we refine the theory of arrays
  virtual void post_process_arrays();
  void arrays_overapproximated();
  
  // we refine expensive arithmetic
  virtual void convert_mult(const exprt &expr, bvt &bv);
  virtual void convert_div(const exprt &expr, bvt &bv);
  virtual void convert_mod(const exprt &expr, bvt &bv);
  virtual void convert_floatbv_op(const exprt &expr, bvt &bv);

  // for collecting statistics
  virtual void set_to(const exprt &expr, bool value);

  // overloading
  virtual void set_assumptions(const bvt &_assumptions);

  bvt parent_assumptions;

  // use gui format
  language_uit::uit ui;

};

#endif
