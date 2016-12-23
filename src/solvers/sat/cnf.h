/*******************************************************************\

Module: CNF Generation, via Tseitin

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_CNF_H
#define CPROVER_SOLVERS_SAT_CNF_H

#include <solvers/prop/prop.h>

class cnft:public propt
{
public:
  // For CNF, we don't use index 0 as a matter of principle,
  // so we'll start counting variables at 1.
  cnft():_no_variables(1) { }
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
  virtual literalt lselect(literalt a, literalt b, literalt c) override; // a?b:c
  virtual literalt new_variable() override;
  virtual size_t no_variables() const override { return _no_variables; }
  virtual void set_no_variables(size_t no) { _no_variables=no; }
  virtual size_t no_clauses() const=0;

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  void gate_xor(literalt a, literalt b, literalt o);
  void gate_nand(literalt a, literalt b, literalt o);
  void gate_nor(literalt a, literalt b, literalt o);
  void gate_equal(literalt a, literalt b, literalt o);
  void gate_implies(literalt a, literalt b, literalt o);

  static bvt eliminate_duplicates(const bvt &);

protected:
  size_t _no_variables;

  bool process_clause(const bvt &bv, bvt &dest);

  static bool is_all(const bvt &bv, literalt l)
  {
    forall_literals(it, bv)
      if(*it!=l) return false;
    return true;
  }
};

class cnf_solvert:public cnft
{
public:
  cnf_solvert():status(INIT), clause_counter(0)
  {
  }

  virtual size_t no_clauses() const override
  {
    return clause_counter;
  }

protected:
  typedef enum { INIT, SAT, UNSAT, ERROR } statust;
  statust status;
  size_t clause_counter;
};

#endif // CPROVER_SOLVERS_SAT_CNF_H
