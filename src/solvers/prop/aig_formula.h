/*******************************************************************\

Module: AND-Inverter Graph Formula

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROPDEC_AIG_FORMULA_H
#define CPROVER_PROPDEC_AIG_FORMULA_H

#include "aig.h"

#if 0
class aig_formulat
{
public:
  aigt aig;
  
  // this is the 'root'
  literalt l;

  literalt convert(propt &dest) const;
  void add_variables(propt &dest) const;
  
  bool is_true() const
  {
    return l.is_true();
  }

  bool is_false() const
  {
    return l.is_false();
  }
  
  void make_false()
  {
    l=const_literal(false);
  }

  void make_true()
  {
    l=const_literal(true);
  }
  
  void swap(aig_formulat &f)
  {
    l.swap(f.l);
    aig.swap(f.aig);
  }
};

std::ostream &operator << (std::ostream &, const aig_formulat &);
#endif

#endif
