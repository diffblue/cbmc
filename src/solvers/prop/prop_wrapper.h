/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_WRAPPER_H
#define CPROVER_PROP_WRAPPER_H

#include "prop.h"

class prop_wrappert:public virtual propt
{
 public:
  prop_wrappert(propt &_prop):propt(_prop), p(_prop) { }
  virtual ~prop_wrappert() { }
  
  virtual literalt constant(bool value)
  { return p.constant(value); }

  // boolean operators
  virtual literalt land(literalt a, literalt b)
  { return p.land(a, b); }

  virtual literalt lor(literalt a, literalt b)
  { return p.lor(a, b); }

  virtual literalt land(const bvt &bv)
  { return p.land(bv); }

  virtual literalt lor(const bvt &bv)
  { return p.lor(bv); }

  virtual literalt lnot(literalt a)
  { return p.lnot(a); }

  virtual literalt lxor(literalt a, literalt b)
  { return p.lxor(a, b); }

  virtual literalt lxor(const bvt &bv)
  { return p.lxor(bv); }

  virtual literalt lnand(literalt a, literalt b)
  { return p.lnand(a, b); }

  virtual literalt lnor(literalt a, literalt b)
  { return p.lnor(a, b); }

  virtual literalt lequal(literalt a, literalt b)
  { return p.lequal(a, b); }

  virtual literalt limplies(literalt a, literalt b)
  { return p.limplies(a, b); }

  virtual literalt lselect(literalt a, literalt b, literalt c) // a?b:c
  { return p.lselect(a, b, c); }

  // constraints
  virtual void lcnf(const bvt &bv)
    { p.lcnf(bv); }

  virtual void l_set_to(literalt a, bool value)
    { p.l_set_to(a, value); }
    
  // literals
  virtual literalt new_variable()
  { return p.new_variable(); }

  virtual unsigned no_variables() const
  { return p.no_variables(); }
  
  // solving
  virtual const std::string solver_text()
  { return p.solver_text(); }

  virtual tvt l_get(literalt a) const
  { return p.l_get(a); }
 
  virtual resultt prop_solve()
  { return p.prop_solve(); }
  
 protected:
  propt &p;
};

#endif
