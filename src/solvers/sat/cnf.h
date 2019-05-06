/*******************************************************************\

Module: CNF Generation, via Tseitin

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CNF Generation, via Tseitin

#ifndef CPROVER_SOLVERS_SAT_CNF_H
#define CPROVER_SOLVERS_SAT_CNF_H

#include <solvers/prop/prop.h>

#include <cstdlib>
#include <vector>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unistd.h>

class cnft:public propt
{
public:
  // For CNF, we don't use index 0 as a matter of principle,
  // so we'll start counting variables at 1.
  explicit cnft(message_handlert &message_handler)
    : propt(message_handler), _no_variables(1)
  {
  }
  virtual ~cnft() { }

  virtual literalt land(literalt a, literalt b) override;
  virtual literalt lor(literalt a, literalt b) override;
  virtual literalt land(const bvt &bv) override;
  virtual literalt lor(const bvt &bv) override;
  virtual literalt lxor(const bvt &bv) override;
  virtual literalt lxor(literalt a, literalt b) override;
  virtual literalt lnand(literalt a, literalt b) override;
  virtual literalt lnor(literalt a, literalt b) override;
  virtual literalt lequal(literalt a, literalt b) override;
  virtual literalt limplies(literalt a, literalt b) override;
  // a?b:c
  virtual literalt lselect(literalt a, literalt b, literalt c) override;
  virtual literalt new_variable() override;
  virtual size_t no_variables() const override { return _no_variables; }
  virtual void set_no_variables(size_t no) { _no_variables=no; }
  virtual size_t no_clauses() const=0;

protected:
  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  void gate_xor(literalt a, literalt b, literalt o);
  void gate_nand(literalt a, literalt b, literalt o);
  void gate_nor(literalt a, literalt b, literalt o);
  void gate_equal(literalt a, literalt b, literalt o);
  void gate_implies(literalt a, literalt b, literalt o);

  static bvt eliminate_duplicates(const bvt &);

  size_t _no_variables;

  bool process_clause(const bvt &bv, bvt &dest);

  static bool is_all(const bvt &bv, literalt l)
  {
    forall_literals(it, bv)
      if(*it!=l)
        return false;
    return true;
  }
};

/** simple container for CNF formula to easily dump it */
class cnf_dumpert
{
  bool active = false;
  std::vector< std::vector<int> > formula;
  std::size_t dumps = 0;
  std::size_t writer = 0;
  std::size_t maxV;
  std::string file_prefix;

  public:
  cnf_dumpert()
  {
    static std::size_t created_writer = 0;
    created_writer++;
    const char *prefix = getenv("CBMC_CNF_DUMP_FILE_PREFIX");
    if(!prefix)
      return;
    active = true;
    file_prefix = prefix;
    writer = created_writer;
  }

  /** add the given clause to the formula */
  void add_clause(const bvt &bv)
  {
    if(!active)
      return;

    formula.emplace_back(std::vector<int>());
    forall_literals(it, bv)
      if(!it->is_false()) {
        maxV = maxV > it->var_no() ? maxV : it->var_no();
        formula.back().push_back(it->sign() ? (-it->var_no()) : (it->var_no()));
      }
  }

  /** dump the CNF to the specified location*/
  void dump_formula(std::string hint = "")
  {
    // make sure different calls get different names
    dumps++;

    std::stringstream filename;
    filename << file_prefix;
    filename << "_" << writer << "_" << dumps << "_" << getpid() << ".cnf";

    std::ofstream out(filename.str());

    if(!out) {
      std::cout << "warn: failed to open file " << filename.str()
                << " for writing" << std::endl;
      return;
    }

    // write header
    out << "c CNF created with CBMC CNF streamer of writer " << writer
        << ", dump " << dumps << std::endl
        << "p cnf " << maxV << " " << formula.size() << std::endl;

    // write formula
    std::size_t count = 0;
    std::stringstream output_block;
    for(const auto &clause : formula)
    {
      // dump clause into string stream (faster than file IO)
      for(const int &l : clause)
        output_block << l << " ";
      output_block << "0" << std::endl;

      // print the block once in a while
      if(++count % CNF_DUMP_BLOCK_SIZE == 0)
      {
        out << output_block.str();
        output_block.str("");
      }
    }

    // make sure the final block is dumped as well
    out << output_block.str();
  }
};

class cnf_solvert:public cnft
{
public:
  explicit cnf_solvert(message_handlert &message_handler)
    : cnft(message_handler), status(statust::INIT), clause_counter(0)
  {
  }

  virtual size_t no_clauses() const override
  {
    return clause_counter;
  }

protected:
  enum class statust { INIT, SAT, UNSAT, ERROR };
  statust status;
  size_t clause_counter;

  cnf_dumpert cnf_dumper;
};

#endif // CPROVER_SOLVERS_SAT_CNF_H
