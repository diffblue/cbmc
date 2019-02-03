/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "dimacs_cnf.h"

#include <util/invariant.h>
#include <util/magic.h>

#include <iostream>
#include <sstream>

dimacs_cnft::dimacs_cnft(message_handlert &message_handler)
  : cnf_clause_listt(message_handler), break_lines(false)
{
}

void dimacs_cnft::set_assignment(literalt, bool)
{
  UNIMPLEMENTED;
}

bool dimacs_cnft::is_in_conflict(literalt) const
{
  UNREACHABLE;
  return false;
}

dimacs_cnf_dumpt::dimacs_cnf_dumpt(
  std::ostream &_out,
  message_handlert &message_handler)
  : cnft(message_handler), out(_out)
{
}

void dimacs_cnft::write_dimacs_cnf(std::ostream &out)
{
  write_problem_line(out);
  write_clauses(out);
}

void dimacs_cnft::write_problem_line(std::ostream &out)
{
  // We start counting at 1, thus there is one variable fewer.
  out << "p cnf " << (no_variables()-1) << " "
      << clauses.size() << "\n";
}

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
    if((j&15)==0 && j!=0 && break_lines)
      out << "\n";
  }

  out << "0" << "\n";
}

void dimacs_cnft::write_clauses(std::ostream &out)
{
  std::size_t count = 0;
  std::stringstream output_block;
  for(clausest::const_iterator it=clauses.begin();
      it!=clauses.end(); it++)
  {
    write_dimacs_clause(*it, output_block, break_lines);

    // print the block once in a while
    if(++count % CNF_DUMP_BLOCK_SIZE == 0)
    {
      out << output_block.str();
      output_block.str("");
    }
  }

  // make sure the final block is printed as well
  out << output_block.str();
}

void dimacs_cnf_dumpt::lcnf(const bvt &bv)
{
  write_dimacs_clause(bv, out, true);
}
