/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROPDEC_LITERAL_H
#define CPROVER_PROPDEC_LITERAL_H

#include <vector>

// a pair of a variable number and a sign, encoded as follows:
//
// sign='false' means positive
// sign='true' means negative
//

class literalt
{
public:
  // constructors
  literalt()
  {
    set(unused_var_no(), false);
  }

  literalt(unsigned v, bool sign)
  {
    set(v, sign);
  }

  class literalt negation() const
  {
    literalt result(*this);
    result.invert();
    return result;
  }
  
  class literalt cond_negation(bool cond) const
  {
    literalt result(*this);
    result.cond_invert(cond);
    return result;
  }
  
  friend inline bool operator ==(const literalt a, const literalt b)
  {
    return a.l==b.l;
  }

  friend inline bool operator !=(const literalt a, const literalt b)
  {
    return a.l!=b.l;
  }

  // for sets  
  friend inline bool operator <(const literalt a, const literalt b)
  {
    return a.l<b.l;
  }
  
  inline unsigned var_no() const
  {
    return l>>1;
  }
  
  inline bool sign() const
  {
    return l&1;
  }
  
  inline void set(unsigned _l)
  {
    l=_l;
  }
  
  inline void set(unsigned v, bool sign)
  {
    l=(v<<1)|((unsigned)sign);
  }
  
  inline unsigned get() const
  {
    return l;
  }
  
  inline void invert()
  {
    l^=1;
  }
  
  inline void cond_invert(bool a)
  {
    l^=(a?1:0);
  }

  //
  // Returns a literal in the dimacs CNF encoding
  // A negative integer denotes a negated literal
  //
  int dimacs() const
  {
    int result=var_no();

    if(sign())
      result=-result;

    return result;
  }
  
  void from_dimacs(int d)
  {
    bool sign=d<0;
    if(sign) d=-d;
    set(d, sign);
  }
  
  void clear()
  {
    l=0;
  }
  
  inline void swap(literalt &x)
  {
    std::swap(x.l, l);
  }
  
  // constants
  inline void make_true()
  {
    set(const_var_no(), true);
  }
  
  inline void make_false()
  {
    set(const_var_no(), false);
  }
  
  inline bool is_true() const
  {
    return is_constant() && sign();
  }
  
  inline bool is_false() const
  {
    return is_constant() && !sign();
  }

  friend inline literalt const_literal(bool value)
  {
    literalt l;
    l.set(literalt::const_var_no(), value);
    return l;
  }
  
  inline bool is_constant() const
  {
    return var_no()==const_var_no();
  }

  friend inline literalt neg(literalt a) { return a.negation(); }
  friend inline literalt pos(literalt a) { return a; }

  static inline unsigned const_var_no()
  {
    return (unsigned(-1)<<1)>>1;
  }

  static inline unsigned unused_var_no()
  {
    return (unsigned(-2)<<1)>>1;
  }

protected:
  unsigned l;  
};

// constants
literalt const_literal(bool value);

literalt neg(literalt a);
literalt pos(literalt a);

typedef std::vector<literalt> bvt;

#define forall_literals(it, bv) \
  for(bvt::const_iterator it=(bv).begin(), it_end=(bv).end(); \
      it!=it_end; ++it)

#define Forall_literals(it, bv) \
  for(bvt::iterator it=(bv).begin(); \
      it!=(bv).end(); ++it)


#endif
