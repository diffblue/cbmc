/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DIMACS_CNF_H
#define CPROVER_DIMACS_CNF_H

#include <ostream>

#include "cnf_clause_list.h"

class dimacs_cnft:public cnf_clause_listt
{
public:
  dimacs_cnft();
  virtual ~dimacs_cnft() { }
 
  virtual void write_dimacs_cnf(std::ostream &out);

  // dummy functions
  
  virtual const std::string solver_text()
  { 
    return "DIMACS CNF";
  }
  
protected:
  void write_problem_line(std::ostream &out);
  void write_clauses(std::ostream &out);
  
  bool break_lines;
};

class dimacs_cnf_dumpt:public cnft
{
public:
  dimacs_cnf_dumpt(std::ostream &_out);
  virtual ~dimacs_cnf_dumpt() { }
 
  virtual const std::string solver_text()
  { 
    return "DIMACS CNF Dumper";
  }
  
  virtual void lcnf(const bvt &bv);

  virtual resultt prop_solve()
  {
    return P_ERROR;
  }

  virtual tvt l_get(literalt) const
  {
    return tvt(tvt::TV_UNKNOWN);
  }
  
  virtual unsigned int no_clauses() const
  {
    return 0;
  }

protected:
  std::ostream &out;
};

#endif
