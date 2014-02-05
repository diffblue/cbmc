/*******************************************************************\

Module: CNF Generation, via Tseitin

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CNF_H
#define CPROVER_PROP_CNF_H

#include <solvers/prop/prop.h>

class cnft:public propt
{
public:
  cnft();
  virtual ~cnft();

  virtual literalt land(literalt a, literalt b);
  virtual literalt lor(literalt a, literalt b);
  virtual literalt land(const bvt &bv);
  virtual literalt lor(const bvt &bv);
  virtual literalt lxor(const bvt &bv);
  virtual literalt lnot(literalt a);
  virtual literalt lxor(literalt a, literalt b);
  virtual literalt lnand(literalt a, literalt b);
  virtual literalt lnor(literalt a, literalt b);
  virtual literalt lequal(literalt a, literalt b);
  virtual literalt limplies(literalt a, literalt b);
  virtual literalt lselect(literalt a, literalt b, literalt c); // a?b:c
  virtual literalt new_variable();
  virtual size_t no_variables() const { return _no_variables; }
  virtual void set_no_variables(size_t no) { _no_variables=no; }
  virtual size_t no_clauses() const=0;

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  void gate_xor(literalt a, literalt b, literalt o);
  void gate_nand(literalt a, literalt b, literalt o);
  void gate_nor(literalt a, literalt b, literalt o);
  void gate_equal(literalt a, literalt b, literalt o);
  void gate_implies(literalt a, literalt b, literalt o);  

  static void eliminate_duplicates(const bvt &bv, bvt &dest);

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
  
  virtual size_t no_clauses() const
  {
    return clause_counter;
  }

protected:
  typedef enum { INIT, SAT, UNSAT, ERROR } statust;
  statust status;
  size_t clause_counter;
}; 

#endif
