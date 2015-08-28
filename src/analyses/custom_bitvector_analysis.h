/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CUSTOM_BITVECTOR_ANALYSIS_H
#define CPROVER_CUSTOM_BITVECTOR_ANALYSIS_H

#include <util/numbering.h>

#include "ai.h"

/*******************************************************************\

   Class: custom_bitvector_domaint
   
 Purpose:

\*******************************************************************/

class custom_bitvector_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  bool merge(
    const custom_bitvector_domaint &b,
    locationt from,
    locationt to);

  void assign_lhs(const exprt &, const exprt &);

  typedef unsigned long long bit_vectort;

  typedef std::map<irep_idt, bit_vectort> bitst;
  bitst bits;

protected:  
  unsigned get_bit_nr(ai_baset &, const exprt &);
  void set_bit(const exprt &, unsigned bit_nr, bool);
};

class custom_bitvector_analysist:public ait<custom_bitvector_domaint> 
{
public:

protected:
  friend class custom_bitvector_domaint;

  numbering<irep_idt> bits;
};

#endif
