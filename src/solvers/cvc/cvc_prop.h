/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CVC_PROP_H
#define CPROVER_PROP_CVC_PROP_H

#include <iostream>

#include <threeval.h>

#include <solvers/prop/prop.h>

class cvc_propt:virtual public propt
{
public:
  cvc_propt(std::ostream &_out);
  virtual ~cvc_propt();

  virtual void land(literalt a, literalt b, literalt o);
  virtual void lor(literalt a, literalt b, literalt o);
  virtual void lxor(literalt a, literalt b, literalt o);
  virtual void lnand(literalt a, literalt b, literalt o);
  virtual void lnor(literalt a, literalt b, literalt o);
  virtual void lequal(literalt a, literalt b, literalt o);
  virtual void limplies(literalt a, literalt b, literalt o);
  
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
  { return "CVC"; }
   
  virtual tvt l_get(literalt literal) const
  {
    unsigned v=literal.var_no();
    if(v>=assignment.size()) return tvt(tvt::TV_UNKNOWN);
    tvt r=assignment[v];
    return literal.sign()?!r:r;
  }
  
  virtual propt::resultt prop_solve();

  friend class cvc_convt;
  friend class cvc_dect;

  virtual void clear()
  {
    assignment.clear();
  }

  void reset_assignment()
  {
    assignment.clear();
    assignment.resize(no_variables(), tvt(tvt::TV_UNKNOWN));
  }

protected:
  unsigned _no_variables;
  std::ostream &out;
  
  std::string cvc_literal(literalt l);
  literalt def_cvc_literal();
  
  std::vector<tvt> assignment;
};

#endif
