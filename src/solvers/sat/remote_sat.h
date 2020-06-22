/*******************************************************************\

Module: Remote SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_REMOTE_SAT_H
#define CPROVER_SOLVERS_SAT_REMOTE_SAT_H

#include "cnf_clause_list.h"

class remote_satt : public cnf_clause_list_assignmentt
{
public:
  explicit remote_satt(message_handlert &message_handler);

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
};

#endif // CPROVER_SOLVERS_SAT_REMOTE_SAT_H
