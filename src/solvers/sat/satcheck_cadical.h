/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H

#include "cnf.h"
#include "xor_propagator.h"

#include <solvers/hardness_collector.h>

#include <memory>
#include <vector>

namespace CaDiCaL // NOLINT(readability/namespace)
{
  class Solver; // NOLINT(readability/identifiers)
}

class cadical_xor_propagator_simplet;

class satcheck_cadical_baset : public cnf_solvert, public hardness_collectort
{
public:
  satcheck_cadical_baset(
    int preprocessing_limit,
    int localsearch_limit,
    message_handlert &);
  virtual ~satcheck_cadical_baset();

  std::string solver_text() const override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  bool has_assumptions() const override
  {
    return true;
  }
  bool has_is_in_conflict() const override
  {
    return true;
  }
  bool is_in_conflict(literalt a) const override;

  /// Record a XOR constraint for Gaussian elimination.
  /// The constraint is: vars[0] XOR vars[1] XOR ... = rhs.
  /// Variables are literalt values (using var_no()).
  void add_xor_constraint(const std::vector<literalt> &lits, bool rhs);

  void register_xor(const bvt &lits, bool rhs) override
  {
    add_xor_constraint(lits, rhs);
  }

  /// Enable XOR Gaussian elimination propagator.
  void enable_xor_gauss();

  void mark_input_variable(literalt lit) override
  {
    unsigned v = lit.var_no();
    if(v >= input_variables.size())
      input_variables.resize(v + 1, false);
    input_variables[v] = true;
  }

  /// Enable aux-first variable renumbering for CaDiCaL.
  void enable_variable_renumbering()
  {
    renumber_variables = true;
  }

#if 0
  literalt new_variable() override;
  bvt new_variables(std::size_t width) override;
#endif

protected:
  resultt do_prop_solve(const bvt &assumptions) override;

  // NOLINTNEXTLINE(readability/identifiers)
  CaDiCaL::Solver *solver;
  int preprocessing_limit = 0, localsearch_limit = 0;
  std::unique_ptr<cadical_xor_propagator_simplet> xor_propagator;
  std::vector<xor_constraintt> pending_xors;
  bool xor_gauss_enabled = false;
  std::size_t xor_constraint_limit = 10000;
  std::vector<bool> input_variables;
  bool renumber_variables = false;
  std::vector<unsigned> var_map;  // old var_no -> new var_no
  std::vector<int> clause_buffer; // flat: lit lit ... 0 lit lit ... 0

  /// Build the variable renumbering map: aux variables get low IDs,
  /// input variables get high IDs.
  void build_variable_map();

  /// Remap a DIMACS literal through the variable map.
  int remap_dimacs(int dimacs_lit) const;
};

class satcheck_cadical_no_preprocessingt : public satcheck_cadical_baset
{
public:
  explicit satcheck_cadical_no_preprocessingt(message_handlert &message_handler)
    : satcheck_cadical_baset(0, 0, message_handler)
  {
  }
};

class satcheck_cadical_preprocessingt : public satcheck_cadical_baset
{
public:
  explicit satcheck_cadical_preprocessingt(message_handlert &message_handler)
    : satcheck_cadical_baset(1, 0, message_handler)
  {
  }
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CADICAL_H
