/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive bitvector analysis

#ifndef CPROVER_ANALYSES_CUSTOM_BITVECTOR_ANALYSIS_H
#define CPROVER_ANALYSES_CUSTOM_BITVECTOR_ANALYSIS_H

#include <util/numbering.h>
#include <util/threeval.h>

#include "ai.h"
#include "local_may_alias.h"

class custom_bitvector_analysist;

class custom_bitvector_domaint:public ai_domain_baset
{
public:
  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final;

  void make_bottom() final
  {
    may_bits.clear();
    must_bits.clear();
    has_values=tvt(false);
  }

  void make_top() final
  {
    may_bits.clear();
    must_bits.clear();
    has_values=tvt(true);
  }

  void make_entry() final
  {
    make_top();
  }

  bool merge(
    const custom_bitvector_domaint &b,
    locationt from,
    locationt to);

  using bit_vectort = unsigned long long;

  using bitst = std::map<irep_idt, bit_vectort>;

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
  void assign_lhs(const irep_idt &, const vectorst &);
  vectorst get_rhs(const exprt &) const;
  vectorst get_rhs(const irep_idt &) const;

  tvt has_values;

  custom_bitvector_domaint():has_values(false)
  {
  }

  static bool has_get_must_or_may(const exprt &);
  exprt eval(
    const exprt &src,
    custom_bitvector_analysist &) const;

private:
  enum class modet { SET_MUST, CLEAR_MUST, SET_MAY, CLEAR_MAY };

  void set_bit(const exprt &, unsigned bit_nr, modet);
  void set_bit(const irep_idt &, unsigned bit_nr, modet);

  static inline void set_bit(bit_vectort &dest, unsigned bit_nr)
  {
    dest|=(1ll<<bit_nr);
  }

  static inline void clear_bit(bit_vectort &dest, unsigned bit_nr)
  {
    dest|=(1ll<<bit_nr);
    dest^=(1ll<<bit_nr);
  }

  static inline bool get_bit(const bit_vectort src, unsigned bit_nr)
  {
    return (src&(1ll<<bit_nr))!=0;
  }

  void erase_blank_vectors(bitst &);

  static irep_idt object2id(const exprt &);
};

class custom_bitvector_analysist:public ait<custom_bitvector_domaint>
{
public:
  void instrument(goto_functionst &);
  void check(
    const goto_modelt &,
    bool xml, std::ostream &);

  exprt eval(const exprt &src, locationt loc)
  {
    return operator[](loc).eval(src, *this);
  }

  unsigned get_bit_nr(const exprt &);

  using bitst = numbering<irep_idt>;
  bitst bits;

protected:
  virtual void initialize(const goto_functionst &_goto_functions)
  {
    ait<custom_bitvector_domaint>::initialize(_goto_functions);
    local_may_alias_factory(_goto_functions);
  }

  friend class custom_bitvector_domaint;

  local_may_alias_factoryt local_may_alias_factory;

  std::set<exprt> aliases(const exprt &, locationt loc);
};

#endif // CPROVER_ANALYSES_CUSTOM_BITVECTOR_ANALYSIS_H
