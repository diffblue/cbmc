/*******************************************************************\

Module: Abstraction Refinement Loop

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstraction Refinement Loop

#ifndef CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H

#include <solvers/flattening/bv_pointers.h>

#define MAX_STATE 10000

class bv_refinementt:public bv_pointerst
{
private:
  struct configt
  {
    bool output_xml = false;
    /// Max number of times we refine a formula node
    unsigned max_node_refinement=5;
    /// Enable array refinement
    bool refine_arrays=true;
    /// Enable arithmetic refinement
    bool refine_arithmetic=true;
  };
public:
  struct infot:public configt
  {
    const namespacet *ns=nullptr;
    propt *prop=nullptr;
  };

  explicit bv_refinementt(const infot &info);

  decision_proceduret::resultt dec_solve() override;

  std::string decision_procedure_text() const override
  {
    return "refinement loop with "+prop.solver_text();
  }

protected:

  // Refine array
  void post_process_arrays() override;

  // Refine arithmetic
  bvt convert_mult(const exprt &expr) override;
  bvt convert_div(const div_exprt &expr) override;
  bvt convert_mod(const mod_exprt &expr) override;
  bvt convert_floatbv_op(const exprt &expr) override;

  void set_assumptions(const bvt &_assumptions) override;

private:
  // the list of operator approximations
  struct approximationt final
  {
  public:
    explicit approximationt(std::size_t _id_nr):
      no_operands(0),
      under_state(0),
      over_state(0),
      id_nr(_id_nr)
    {
    }

    exprt expr;
    std::size_t no_operands;

    bvt op0_bv, op1_bv, op2_bv, result_bv;
    mp_integer op0_value, op1_value, op2_value, result_value;

    bvt under_assumptions;
    bvt over_assumptions;

    // the kind of under- or over-approximation
    unsigned under_state, over_state;

    std::string as_string() const;

    void add_over_assumption(literalt l);
    void add_under_assumption(literalt l);

    std::size_t id_nr;
  };

  resultt prop_solve();
  approximationt &add_approximation(const exprt &expr, bvt &bv);
  bool conflicts_with(approximationt &approximation);
  void check_SAT(approximationt &approximation);
  void check_UNSAT(approximationt &approximation);
  void initialize(approximationt &approximation);
  void get_values(approximationt &approximation);
  void check_SAT();
  void check_UNSAT();
  void arrays_overapproximated();
  void freeze_lazy_constraints();

  // MEMBERS

  bool progress;
  std::list<approximationt> approximations;
  bvt parent_assumptions;
protected:
  // use gui format
  configt config_;
};

#endif // CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H
