/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROPDEC_BFORMULA_H
#define CPROVER_PROPDEC_BFORMULA_H

#include "prop.h"

class bformulat
{
protected:
  literalt l;
  propt *prop;

public:
  // constructors
  bformulat():prop(NULL)
  {
  }

  friend bformulat operator! (bformulat f)
  {
    f.l.invert();
    return f;
  }
  
  friend bformulat operator? (
    bformulat c, bformulat a, bformulat b);

  friend bformulat operator | (bformulat a, bformulat b);
  friend bformulat operator & (bformulat a, bformulat b);
  friend bformulat operator ^ (bformulat a, bformulat b);
  friend bformulat operator ==(bformulat a, bformulat b);
  friend bformulat operator !=(bformulat a, bformulat b);

  // for sets  
  friend inline bool operator <(const bformulat a, const bformulat b)
  {
    return a.l<b.l;
  }
  
  inline unsigned var_no() const
  {
    return l.var_no();
  }
  
  inline bool sign() const
  {
    return l.sign();
  }
  
  inline void set(literalt _l)
  {
    l=_l;
  }
  
  inline void set(unsigned v, bool sign)
  {
    l.set(v, sign);
  }
  
  inline literalt get_literal() const
  {
    return l;
  }
  
  void clear()
  {
    l.clear();
    prop=NULL;
  }
  
  inline void swap(bformulat &x)
  {
    std::swap(x.l, l);
    std::swap(x.prop, prop);
  }
  
  // constants
  inline void make_true()
  {
    l.make_true();
  }
  
  inline void make_false()
  {
    l.make_false();
  }
  
  inline bool is_true() const
  {
    return l.is_true();
  }
  
  inline bool is_false() const
  {
    return l.is_false();
  }

  inline tvt value() const
  {
    return prop->l_get(l);
  }

  friend inline bformulat const_bformula(bool value)
  {
    bformulat f;
    f.l=const_literal(value);
    return f;
  }
  
  inline bool is_constant() const
  {
    return l.is_constant();
  }
};

// constants
bformulat const_bformula(bool value);

//typedef std::vector<bformulat> bvt;

#endif
