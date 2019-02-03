/*******************************************************************\

Module: CNF Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CNF Generation

#ifndef CPROVER_SOLVERS_SAT_CNF_CLAUSE_LIST_H
#define CPROVER_SOLVERS_SAT_CNF_CLAUSE_LIST_H

#include <list>

#include <util/threeval.h>

#include "cnf.h"

// CNF given as a list of clauses

class cnf_clause_listt:public cnft
{
public:
  explicit cnf_clause_listt(message_handlert &message_handler)
    : cnft(message_handler)
  {
  }
  virtual ~cnf_clause_listt() { }

  void lcnf(const bvt &bv) override;

  const std::string solver_text() override
  { return "CNF clause list"; }

  tvt l_get(literalt) const override
  {
    return tvt::unknown();
  }

  resultt prop_solve() override
  {
    return resultt::P_ERROR;
  }

  size_t no_clauses() const override
  {
    return clauses.size();
  }

  typedef std::list<bvt> clausest;

  clausest &get_clauses() { return clauses; }

  void copy_to(cnft &cnf) const
  {
    cnf.set_no_variables(_no_variables);
    for(clausest::const_iterator
        it=clauses.begin();
        it!=clauses.end();
        it++)
      cnf.lcnf(*it);
  }

  static size_t hash_clause(const bvt &bv)
  {
    size_t result=0;
    for(bvt::const_iterator it=bv.begin(); it!=bv.end(); it++)
      result=((result<<2)^it->get())-result;

    return result;
  }

  size_t hash() const
  {
    size_t result=0;
    for(clausest::const_iterator it=clauses.begin(); it!=clauses.end(); it++)
      result=((result<<2)^hash_clause(*it))-result;

    return result;
  }

protected:
  clausest clauses;
};

// CNF given as a list of clauses
// PLUS an assignment to the variables

class cnf_clause_list_assignmentt:public cnf_clause_listt
{
public:
  explicit cnf_clause_list_assignmentt(message_handlert &message_handler)
    : cnf_clause_listt(message_handler)
  {
  }

  typedef std::vector<tvt> assignmentt;

  assignmentt &get_assignment()
  {
    return assignment;
  }

  tvt l_get(literalt literal) const override
  {
    if(literal.is_true())
      return tvt(true);
    if(literal.is_false())
      return tvt(false);

    unsigned v=literal.var_no();

    if(v==0 || v>=assignment.size())
      return tvt::unknown();

    tvt r=assignment[v];
    return literal.sign()?!r:r;
  }

  virtual void copy_assignment_from(const propt &prop);
  void print_assignment(std::ostream &out) const;

protected:
  assignmentt assignment;
};

#endif // CPROVER_SOLVERS_SAT_CNF_CLAUSE_LIST_H
