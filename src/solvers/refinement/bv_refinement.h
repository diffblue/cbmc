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

/// Configuration and info for the refinement solver.
/// Separated from the class template so callers don't need
/// to know the template parameter.
struct bv_refinement_configt
{
  bool output_xml = false;
  unsigned max_node_refinement = 5;
  bool refine_arrays = true;
  bool refine_arithmetic = true;
};

struct bv_refinement_infot : public bv_refinement_configt
{
  const namespacet *ns = nullptr;
  propt *prop = nullptr;
  message_handlert *message_handler = nullptr;
};

/// Abstraction refinement loop, parameterized on the pointer
/// encoding base class.  The default is bv_pointerst (standard
/// bit-packed encoding).  Use bv_pointers_widet for the map-based
/// encoding.
template <typename bv_pointers_baset = bv_pointerst>
class bv_refinementt : public bv_pointers_baset
{
public:
  using resultt = decision_proceduret::resultt;

  // Keep the old infot name for backward compatibility
  using infot = bv_refinement_infot;

  explicit bv_refinementt(const infot &info);

  resultt dec_solve(const exprt &) override;

  std::string decision_procedure_text() const override
  {
    return "refinement loop with " + bv_pointers_baset::prop.solver_text();
  }

protected:
  // Refine array
  void finish_eager_conversion_arrays() override;

  // Refine arithmetic
  bvt convert_mult(const mult_exprt &expr) override;
  bvt convert_div(const div_exprt &expr) override;
  bvt convert_mod(const mod_exprt &expr) override;
  bvt convert_floatbv_op(const ieee_float_op_exprt &) override;

private:
  // the list of operator approximations
  struct approximationt final
  {
  public:
    explicit approximationt(std::size_t _id_nr)
      : no_operands(0), under_state(0), over_state(0), id_nr(_id_nr)
    {
    }

    exprt expr;
    std::size_t no_operands;

    bvt op0_bv, op1_bv, op2_bv, result_bv;
    mp_integer op0_value, op1_value, op2_value, result_value;

    std::vector<exprt> under_assumptions;
    std::vector<exprt> over_assumptions;

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

  bool progress;
  std::list<approximationt> approximations;

protected:
  bv_refinement_configt config_;
};

#endif // CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H
