/// \file
/// SAT solver backend using CryptoMiniSat with native XOR support.

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_CRYPTOMINISAT_H
#define CPROVER_SOLVERS_SAT_SATCHECK_CRYPTOMINISAT_H

#include "cnf.h"

namespace CMSat // NOLINT(readability/namespace)
{
class SATSolver; // NOLINT(readability/identifiers)
} // namespace CMSat

class satcheck_cryptominisatt : public cnf_solvert
{
public:
  explicit satcheck_cryptominisatt(message_handlert &);
  ~satcheck_cryptominisatt() override;

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

  void register_xor(const bvt &lits, bool rhs) override;

  literalt new_variable() override;
  bvt new_variables(std::size_t width) override;

protected:
  resultt do_prop_solve(const bvt &assumptions) override;

private:
  CMSat::SATSolver *solver;

  struct xor_constraintt
  {
    std::vector<unsigned> vars;
    bool rhs;
  };
  std::vector<xor_constraintt> pending_xors;
  bool xors_added = false;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_CRYPTOMINISAT_H
