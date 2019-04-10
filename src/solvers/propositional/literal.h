/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_LITERAL_H
#define CPROVER_SOLVERS_PROP_LITERAL_H

#include <iosfwd>
#include <util/narrow.h>
#include <vector>

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
  // We deliberately don't use size_t here to save some memory
  // on 64-bit machines; i.e., in practice, we restrict ourselves
  // to SAT instances with no more than 2^31 variables.
  typedef unsigned var_not;

  // constructors
  literalt()
  {
    set(unused_var_no(), false);
  }

  literalt(var_not v, bool sign)
  {
    set(v, sign);
  }

  bool operator==(const literalt other) const
  {
    return l==other.l;
  }

  bool operator!=(const literalt other) const
  {
    return l!=other.l;
  }

  // for sets
  bool operator<(const literalt other) const
  {
    return l<other.l;
  }

  // negates if 'b' is true
  literalt operator^(const bool b) const
  {
    literalt result(*this);
    result.l^=(var_not)b;
    return result;
  }

  // negates the literal
  literalt operator!() const
  {
    literalt result(*this);
    result.invert();
    return result;
  }

  literalt operator^=(const bool a)
  {
    // we use the least significant bit to store the sign
    l^=(var_not)a;
    return *this;
  }

  var_not var_no() const
  {
    return l>>1;
  }

  bool sign() const
  {
    return l&1;
  }

  void set(var_not _l)
  {
    l=_l;
  }

  void set(var_not v, bool sign)
  {
    l=(v<<1)|((var_not)sign);
  }

  var_not get() const
  {
    return l;
  }

  void invert()
  {
    l^=(var_not)1;
  }

  //
  // Returns a literal in the dimacs CNF encoding.
  // A negative integer denotes a negated literal.
  //
  int dimacs() const
  {
    int result = narrow_cast<int>(var_no());

    if(sign())
      result=-result;

    return result;
  }

  void from_dimacs(int d)
  {
    bool sign=d<0;
    if(sign)
      d=-d;
    set(narrow_cast<unsigned>(d), sign);
  }

  void clear()
  {
    l=0;
  }

  void swap(literalt &x)
  {
    std::swap(x.l, l);
  }

  // constants
  void make_true()
  {
    set(const_var_no(), true);
  }

  void make_false()
  {
    set(const_var_no(), false);
  }

  bool is_true() const
  {
    return is_constant() && sign();
  }

  bool is_false() const
  {
    return is_constant() && !sign();
  }

  bool is_constant() const
  {
    return var_no()==const_var_no();
  }

  static inline var_not const_var_no()
  {
    return (var_not(-1)<<1)>>1;
  }

  static inline var_not unused_var_no()
  {
    return (var_not(-2)<<1)>>1;
  }

protected:
  var_not l;
};

std::ostream &operator << (std::ostream &out, literalt l);

// constants
inline literalt const_literal(bool value)
{
  return literalt(literalt::const_var_no(), value);
}

inline literalt neg(literalt a) { return !a; }
inline literalt pos(literalt a) { return a; }


inline bool is_false (const literalt &l) { return (l.is_false()); }
inline bool is_true (const literalt &l) { return (l.is_true()); }

// bit-vectors
typedef std::vector<literalt> bvt;

#define forall_literals(it, bv) \
  for(bvt::const_iterator it=(bv).begin(), it_end=(bv).end(); \
      it!=it_end; ++it)

#define Forall_literals(it, bv) \
  for(bvt::iterator it=(bv).begin(); \
      it!=(bv).end(); ++it)

#endif // CPROVER_SOLVERS_PROP_LITERAL_H
