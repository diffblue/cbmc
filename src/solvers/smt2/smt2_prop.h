/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_SMT2_PROP_H
#define CPROVER_PROP_SMT2_PROP_H

#include <iostream>

#include <threeval.h>

#include <solvers/prop/prop.h>

class smt2_propt:public propt
{
public:
  smt2_propt(
    const std::string &_benchmark,
    const std::string &_source,
    const std::string &_logic,
    std::ostream &_out);
  virtual ~smt2_propt();

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
  virtual unsigned no_variables() const { return _no_variables; }
  virtual void set_no_variables(unsigned no) { assert(false); }

  virtual void lcnf(const bvt &bv);

  virtual const std::string solver_text()
  { return "SMT"; }
   
  virtual tvt l_get(literalt literal) const;
  virtual void set_assignment(literalt a, bool value);

  virtual propt::resultt prop_solve();

  virtual void clear()
  {
    assignment.clear();
  }

  virtual void reset_assignment()
  {
    assignment.clear();
    assignment.resize(no_variables(), tvt(tvt::TV_UNKNOWN));
  }

  friend class smt2_convt;
  friend class smt2_dect;
  
  void finalize();

protected:
  unsigned _no_variables;
  std::ostream &out;
  
  std::string smt2_literal(literalt l);
  literalt def_smt2_literal();
  
  std::vector<tvt> assignment;
  
  literalt define_new_variable();
};

#endif
