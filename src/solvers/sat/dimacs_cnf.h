/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_DIMACS_CNF_H
#define CPROVER_SOLVERS_SAT_DIMACS_CNF_H

#include <iosfwd>
#include <atomic>
#include <condition_variable>

#include "cnf_clause_list.h"
#include <util/blocking_queue.h>

class dimacs_cnft:public cnf_clause_listt
{
protected:
  // Optimal block size, in clauses
  const size_t target_block_size = 1<<16;

  struct clause_range {
    size_t ordinal;
    clausest::const_iterator first, limit;
    explicit clause_range(const size_t ordinal,
                          const clausest::const_iterator first,
                          const clausest::const_iterator limit)
      : ordinal(ordinal), first(first), limit(limit)
    { }
    clause_range() : ordinal(0), first(nullptr), limit(nullptr) { }
  };

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

  static void
  write_dimacs_clause(const bvt &, std::ostream &, bool break_lines);

protected:
  void write_problem_line(std::ostream &out);
  void write_clauses(std::ostream &out);
  void wait_file_block(const size_t ordinal);
  void printer_entry(std::ostream *out);

  bool break_lines;
  size_t next_file_block;
  std::mutex writing_sync;
  std::condition_variable block_written;
  blocking_queue<clause_range> print_queue;
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

  tvt l_get(literalt) const override
  {
    return tvt::unknown();
  }

  size_t no_clauses() const override
  {
    return 0;
  }

protected:
  resultt do_prop_solve() override
  {
    return resultt::P_ERROR;
  }

  std::ostream &out;
};

#endif // CPROVER_SOLVERS_SAT_DIMACS_CNF_H
