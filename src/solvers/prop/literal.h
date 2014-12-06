/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROPDEC_LITERAL_H
#define CPROVER_PROPDEC_LITERAL_H

#include <vector>
#include <iosfwd>

// a pair of a variable number and a sign, encoded as follows:
//
// sign='false' means positive
// sign='true' means negative
//
// The top bit is used to indicate that the literal is constant
// true or false.

class literalt
{
public:
  // constructors
  inline literalt()
  {
    set(unused_var_no(), false);
  }

  inline literalt(unsigned v, bool sign)
  {
    set(v, sign);
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

  // negates if 'b' is true  
  friend inline literalt operator^(const literalt a, const bool b)
  {
    literalt result=a;
    result.l^=(unsigned)b;
    return result;
  }

  // negates the literal
  friend inline literalt operator!(const literalt a)
  {
    literalt result(a);
    result.invert();
    return result;
  }

  inline literalt operator^=(const bool a)
  {
    // we use the least significant bit to store the sign
    l^=(unsigned)a;
    return *this;
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
    l^=(unsigned)1;
  }

  //
  // Returns a literal in the dimacs CNF encoding.
  // A negative integer denotes a negated literal.
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
  
  inline void clear()
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
    return literalt(literalt::const_var_no(), value);
  }
  
  inline bool is_constant() const
  {
    return var_no()==const_var_no();
  }

  friend inline literalt neg(literalt a) { return !a; }
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
  // We deliberately don't use size_t here to save some memory
  // on 64-bit machines; i.e., in practice, we restrict ourselves
  // to SAT instances with no more than 2^31 variables.
  unsigned l;  
};

std::ostream & operator << (std::ostream &out, literalt l);

// constants
literalt const_literal(bool value);

literalt neg(literalt a);
literalt pos(literalt a);

// bit-vectors
typedef std::vector<literalt> bvt;

#define forall_literals(it, bv) \
  for(bvt::const_iterator it=(bv).begin(), it_end=(bv).end(); \
      it!=it_end; ++it)

#define Forall_literals(it, bv) \
  for(bvt::iterator it=(bv).begin(); \
      it!=(bv).end(); ++it)

#endif
