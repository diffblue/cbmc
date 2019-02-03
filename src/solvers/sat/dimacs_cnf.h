/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_DIMACS_CNF_H
#define CPROVER_SOLVERS_SAT_DIMACS_CNF_H

#include <iosfwd>

#include "cnf_clause_list.h"

class dimacs_cnft:public cnf_clause_listt
{
public:
  explicit dimacs_cnft(message_handlert &);
  virtual ~dimacs_cnft() { }

  virtual void write_dimacs_cnf(std::ostream &out);

  // dummy functions

  const std::string solver_text() override
  {
    return "DIMACS CNF";
  }

  void set_assignment(literalt a, bool value) override;
  bool is_in_conflict(literalt l) const override;

protected:
  void write_problem_line(std::ostream &out);
  void write_clauses(std::ostream &out);

  bool break_lines;
};

class dimacs_cnf_dumpt:public cnft
{
public:
  dimacs_cnf_dumpt(std::ostream &_out, message_handlert &message_handler);
  virtual ~dimacs_cnf_dumpt() { }

  const std::string solver_text() override
  {
    return "DIMACS CNF Dumper";
  }

  void lcnf(const bvt &bv) override;

  resultt prop_solve() override
  {
    return resultt::P_ERROR;
  }

  tvt l_get(literalt) const override
  {
    return tvt::unknown();
  }

  size_t no_clauses() const override
  {
    return 0;
  }

protected:
  std::ostream &out;
};

#endif // CPROVER_SOLVERS_SAT_DIMACS_CNF_H
