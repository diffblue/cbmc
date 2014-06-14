/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "dimacs_cnf.h"

#include <iostream>

/*******************************************************************\

Function: dimacs_cnft::dimacs_cnft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dimacs_cnft::dimacs_cnft():break_lines(false)
{
}

/*******************************************************************\

Function: dimacs_cnf_dumpt::dimacs_cnf_dumpt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dimacs_cnf_dumpt::dimacs_cnf_dumpt(std::ostream &_out):out(_out)
{
}

/*******************************************************************\

Function: dimacs_cnft::write_dimacs_cnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dimacs_cnft::write_dimacs_cnf(std::ostream &out)
{
  write_problem_line(out);
  write_clauses(out);
}

/*******************************************************************\

Function: dimacs_cnft::write_problem_line

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dimacs_cnft::write_problem_line(std::ostream &out)
{
  out << "p cnf " << no_variables() << " " 
      << clauses.size() << "\n";
}

/*******************************************************************\

Function: write_dimacs_clause

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void write_dimacs_clause(
  const bvt &clause,
  std::ostream &out,
  bool break_lines)
{
  // The DIMACS CNF format allows line breaks in clauses:
  // "Each clauses is terminated by the value 0. Unlike many formats
  // that represent the end of a clause by a new-line character,
  // this format allows clauses to be on multiple lines."
  // Some historic solvers (zchaff e.g.) have silently swallowed
  // literals in clauses that exceed some fixed buffer size.
  
  // However, the SAT competition format does not allow line
  // breaks in clauses, so we offer both options. 

  for(size_t j=0; j<clause.size(); j++)
  {
    out << clause[j].dimacs() << " ";
    // newline to avoid overflow in sat checkers
    if((j&15)==0 && j!=0 && break_lines) out << "\n";
  }

  out << "0" << "\n";
}

/*******************************************************************\

Function: dimacs_cnft::write_clauses

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dimacs_cnft::write_clauses(std::ostream &out)
{
  for(clausest::const_iterator it=clauses.begin();
      it!=clauses.end(); it++)
    write_dimacs_clause(*it, out, break_lines);
}

/*******************************************************************\

Function: dimacs_cnf_dumpt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dimacs_cnf_dumpt::lcnf(const bvt &bv)
{
  write_dimacs_clause(bv, out, true);
}

