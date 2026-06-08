/*******************************************************************\

Module: Abstraction Refinement Loop

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstraction Refinement Loop

#ifndef CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H

#include <solvers/flattening/bv_pointers.h>

#include <cstdlib>

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
    message_handlert *message_handler = nullptr;
  };

  explicit bv_refinementt(const infot &info);

  decision_proceduret::resultt dec_solve(const exprt &) override;

  std::string decision_procedure_text() const override
  {
    return "refinement loop with "+prop.solver_text();
  }

protected:

  // Refine array
  void finish_eager_conversion_arrays() override;

  // Refine arithmetic
  bvt convert_mult(const mult_exprt &expr) override;
  bvt convert_div(const div_exprt &expr) override;
  bvt convert_mod(const mod_exprt &expr) override;
  bvt convert_floatbv_op(const ieee_float_op_exprt &) override;

  // Composition of pair detection (this layer) with Paper 2's
  // algebraic Gröbner-basis layer (in boolbvt::try_algebraic_solve):
  // by default both run. Pair detection is cheap (one walk of the
  // approximation list); the algebraic layer can solve cleanly
  // polynomial-shaped problems (e.g. SMT-LIB varscale at high k)
  // faster than refinement with pair detection alone. The combined
  // pipeline is a strict superset.
  //
  // Users who know their input is laundered through opaque
  // computation (e.g. C-input multiplications through store/load)
  // can set CBMC_REFINE_SKIP_ALG=1 to skip the algebraic layer and
  // save its failed-attempt overhead (~1 s in those cases).
  bool try_algebraic_solve() override
  {
    if(config_.refine_arithmetic)
    {
      const char *skip_env = std::getenv("CBMC_REFINE_SKIP_ALG");
      if(skip_env != nullptr && skip_env[0] != '\0' && skip_env[0] != '0')
      {
        return false;
      }
    }
    return boolbvt::try_algebraic_solve();
  }

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

    std::vector<exprt> under_assumptions;
    std::vector<exprt> over_assumptions;

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
  /// Find commutative/associative/distributive multiplier
  /// equivalences and assert result equality at the bit level.
  /// Returns the total number of equality constraints emitted
  /// (commutative pairs plus distributive triples). Callers can use
  /// the return value to decide whether the refinement-loop
  /// architecture is justified for the query: when zero
  /// equivalences are found, \ref dec_solve falls back to direct
  /// bit-blasting via \ref eagerly_complete_approximations rather
  /// than entering the refinement loop.
  std::size_t detect_algebraic_pairs();
  /// Assert exact bit-blasted multiplication semantics for every
  /// approximation. After this call the refinement loop is
  /// effectively bypassed because no over/under-approximation can
  /// contradict the exact constraint. Used as a fallback when
  /// pair detection finds no useful equivalences.
  void eagerly_complete_approximations();
  void arrays_overapproximated();
  void freeze_lazy_constraints();

  // MEMBERS

  bool progress;
  std::list<approximationt> approximations;

protected:
  // use gui format
  configt config_;
};

#endif // CPROVER_SOLVERS_REFINEMENT_BV_REFINEMENT_H
