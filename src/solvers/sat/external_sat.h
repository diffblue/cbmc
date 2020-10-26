/// \file
/// Allows calling an external SAT solver to allow faster integration of
/// newer SAT solvers
/// \author Francis Botero <fbbotero@amazon.com>

#ifndef CPROVER_SOLVERS_SAT_EXTERNAL_SAT_H
#define CPROVER_SOLVERS_SAT_EXTERNAL_SAT_H

#include "cnf_clause_list.h"
class external_satt : public cnf_clause_list_assignmentt
{
public:
  explicit external_satt(message_handlert &message_handler, std::string cmd);

  bool has_set_assumptions() const override final
  {
    return true;
  }

  bool has_is_in_conflict() const override final
  {
    return false;
  }

  const std::string solver_text() override;

  bool is_in_conflict(literalt) const override;
  void set_assignment(literalt, bool) override;

  void set_assumptions(const bvt &_assumptions) override
  {
    assumptions = _assumptions;
  }

protected:
  std::string solver_cmd;
  bvt assumptions;

  resultt do_prop_solve() override;
  void write_cnf_file(std::string);
  std::string execute_solver(std::string);
  resultt parse_result(std::string);
};

#endif // CPROVER_SOLVERS_SAT_EXTERNAL_SAT_H
