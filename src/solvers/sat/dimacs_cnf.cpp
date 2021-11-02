/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "dimacs_cnf.h"

#include <util/invariant.h>
#include <util/magic.h>

#include <iostream>
#include <thread>

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

void dimacs_cnft::write_dimacs_clause(
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

void dimacs_cnft::wait_file_block(const size_t ordinal) {
  std::unique_lock<std::mutex> lock(writing_sync);
  for(;;) {
    assert(next_file_block <= ordinal);
    if(next_file_block == ordinal) {
      return;
    }
    block_written.wait(lock);
  }
}

void dimacs_cnft::printer_entry(std::ostream *out) {
  clause_range item;
  std::stringstream output_block;
  while(print_queue.pop(item)) {
    output_block.str("");
    output_block.clear();

    for(clausest::const_iterator it=item.first; it!=item.limit; it++) {
      write_dimacs_clause(*it, output_block, break_lines);
    }

    wait_file_block(item.ordinal);
    *out << output_block.str();
    std::unique_lock<std::mutex> lock(writing_sync);
    next_file_block++;
    block_written.notify_all();
  }
}

void dimacs_cnft::write_clauses(std::ostream &out)
{
  std::vector<std::thread> pool;
  const size_t thread_count = std::max(2u, std::thread::hardware_concurrency()) - 1;
  for(size_t i=0; i<thread_count; i++) {
    pool.emplace_back(&dimacs_cnft::printer_entry, this, &out);
  }
  next_file_block = 0;
  size_t total_blocks = 0;
  for(clausest::const_iterator it=clauses.begin();
      it!=clauses.end(); )
  {
    clausest::const_iterator first = it;
    size_t total_size = 0;
    while(total_size < target_block_size && it != clauses.end()) {
      total_size += it->size();
      it++;
    }
    print_queue.push(clause_range(total_blocks, first, it));
    total_blocks++;
  }
  print_queue.request_shutdown();
  wait_file_block(total_blocks);
  for(size_t i=0; i<pool.size(); i++) {
    pool[i].join();
  }
}

void dimacs_cnf_dumpt::lcnf(const bvt &bv)
{
  dimacs_cnft::write_dimacs_clause(bv, out, true);
}
