/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CUSTOM_BITVECTOR_ANALYSIS_H
#define CPROVER_CUSTOM_BITVECTOR_ANALYSIS_H

#include <util/numbering.h>

#include "ai.h"
#include "local_may_alias.h"

/*******************************************************************\

   Class: custom_bitvector_domaint
   
 Purpose:

\*******************************************************************/

class custom_bitvector_analysist;

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

  virtual void make_bottom()
  {
    may_bits.clear();
    must_bits.clear();
    is_bottom=true;
  }

  virtual void make_top()
  {
    may_bits.clear();
    must_bits.clear();
    is_bottom=false;
  }

  bool merge(
    const custom_bitvector_domaint &b,
    locationt from,
    locationt to);

  typedef unsigned long long bit_vectort;
  typedef std::map<irep_idt, bit_vectort> bitst;
  
  struct vectorst
  {
    bit_vectort may_bits, must_bits;
    vectorst():may_bits(0), must_bits(0)
    {
    }
  };
  
  static vectorst merge(const vectorst &a, const vectorst &b)
  {
    vectorst result;
    result.may_bits=a.may_bits|b.may_bits;
    result.must_bits=a.must_bits&b.must_bits;
    return result;
  }
  
  bitst may_bits, must_bits;
  
  void assign_lhs(const exprt &, const vectorst &);
  vectorst get_rhs(const exprt &) const;
  vectorst get_rhs(const irep_idt &) const;

  bool is_bottom;
  
  custom_bitvector_domaint():is_bottom(true)
  {
  }

  static bool has_get_must_or_may(const exprt &);
  exprt eval(
    const exprt &src,
    custom_bitvector_analysist &) const;

protected:  
  typedef enum { SET_MUST, CLEAR_MUST, SET_MAY, CLEAR_MAY } modet;

  void set_bit(const exprt &, unsigned bit_nr, modet);
  void set_bit(const irep_idt &, unsigned bit_nr, modet);
};

class custom_bitvector_analysist:public ait<custom_bitvector_domaint> 
{
public:
  void instrument(goto_functionst &);
  void check(const namespacet &, const goto_functionst &, bool xml, std::ostream &);

  exprt eval(const exprt &src, locationt loc)
  {
    return operator[](loc).eval(src, *this);
  }

  unsigned get_bit_nr(const exprt &);

protected:
  virtual void initialize(const goto_functionst &_goto_functions)
  {
    local_may_alias_factory(_goto_functions);
  }

  friend class custom_bitvector_domaint;

  numbering<irep_idt> bits;
  
  local_may_alias_factoryt local_may_alias_factory;
};

#endif
