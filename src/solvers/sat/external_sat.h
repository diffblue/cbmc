/*******************************************************************\

Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_EXTERNAL_SAT_SAT_H
#define CPROVER_SOLVERS_EXTERNAL_SAT_SAT_H

#include "cnf_clause_list.h"
/// \brief Allows call an external SAT solver to allow faster integration of newer SAT solvers
class external_satt : public cnf_clause_list_assignmentt
{
public:
  explicit external_satt(message_handlert &message_handler, std::string cmd);

  bool has_set_assumptions() const override final
  {
    return false;
  }

  bool has_is_in_conflict() const override final
  {
    return false;
  }

  const std::string solver_text() override;

  bool is_in_conflict(literalt) const override;
  void set_assignment(literalt, bool) override;

protected:
  resultt do_prop_solve() override;
  std::string _cmd;

private:
  inline void write_cnf_file(std::string);
  inline std::string execute_solver(std::string);
  inline resultt parse_result(std::string);
};

#endif // CPROVER_SOLVERS_EXTERNAL_SAT_SAT_H
