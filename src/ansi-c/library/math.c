/* FUNCTION: fabs */

inline double fabs(double d) { return __CPROVER_fabs(d); }

/* FUNCTION: fabsl */

inline long double fabsl(long double d) { return __CPROVER_fabsl(d); }

/* FUNCTION: fabsf */

inline float fabsf(float f) { return __CPROVER_fabsf(f); }

/* FUNCTION: __builtin_fabs */

inline double __builtin_fabs(double d) { return __CPROVER_fabs(d); }

/* FUNCTION: __builtin_fabsl */

inline long double __builtin_fabsl(long double d) { return __CPROVER_fabsl(d); }

/* FUNCTION: __builtin_fabsf */

inline float __builtin_fabsf(float f) { return __CPROVER_fabsf(f); }

/* FUNCTION: isfinite */

int isfinite(double d) { return __CPROVER_isfinite(d); }

/* FUNCTION: __finite */

int __finite(double d) { return __CPROVER_isfinite(d); }

/* FUNCTION: __finitef */

int __finitef(float f) { return __CPROVER_isfinite(f); }

/* FUNCTION: __finitel */

int __finitel(long double d) { return __CPROVER_isfinite(d); }

/* FUNCTION: isinf */

inline int isinf(double d) { return __CPROVER_isinf(d); }

/* FUNCTION: __isinf */

inline int __isinf(double d) { return __CPROVER_isinf(d); }

/* FUNCTION: isinff */

inline int isinff(float f) { return __CPROVER_isinf(f); }

/* FUNCTION: __isinff */

inline int __isinff(float f) { return __CPROVER_isinf(f); }

/* FUNCTION: isinfl */

inline int isinfl(long double d) { return __CPROVER_isinf(d); }

/* FUNCTION: __isinfl */

inline int __isinfl(long double d) { return __CPROVER_isinf(d); }

/* FUNCTION: isnan */

inline int isnan(double d) { return __CPROVER_isnan(d); }

/* FUNCTION: __isnan */

inline int __isnan(double d) { return __CPROVER_isnan(d); }

/* FUNCTION: __isnanf */

inline int __isnanf(float f) { return __CPROVER_isnan(f); }

/* FUNCTION: isnanf */

inline int isnanf(float f) { return __CPROVER_isnan(f); }

/* FUNCTION: isnanl */

inline int isnanl(long double d) { return __CPROVER_isnan(d); }

/* FUNCTION: __isnanl */

inline int __isnanl(long double d) { return __CPROVER_isnan(d); }

/* FUNCTION: isnormal */

int isnormal(double d) { return __CPROVER_isnormal(d); }

/* FUNCTION: __builtin_inff */

float __builtin_inff(void) { return 1.0f/0.0f; }

/* FUNCTION: __builtin_inf */

double __builtin_inf(void) { return 1.0/0.0; }

/* FUNCTION: __builtin_infl */

long double __builtin_infl(void) { return 1.0l/0.0l; }

/* FUNCTION: __builtin_huge_valf */

float __builtin_huge_valf(void) { return 1.0f/0.0f; }

/* FUNCTION: __builtin_huge_val */

double __builtin_huge_val(void) { return 1.0/0.0; }

/* FUNCTION: __builtin_huge_vall */

long double __builtin_huge_vall(void) { return 1.0l/0.0l; }

/* FUNCTION: signbit */

inline int signbit(double d) { return __CPROVER_sign(d); }

/* FUNCTION: __signbitf */

inline int __signbitf(float f) { return __CPROVER_sign(f); }

/* FUNCTION: __signbit */

inline int __signbit(double d) { return __CPROVER_sign(d); }

/* FUNCTION: __fpclassifyd */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyd(double d) {
  __CPROVER_HIDE:
  return __CPROVER_isnan(d)?FP_NAN:
         __CPROVER_isinf(d)?FP_INFINITE:
         d==0?FP_ZERO:
         __CPROVER_isnormal(d)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: __fpclassifyf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyf(float f) {
  __CPROVER_HIDE:
  return __CPROVER_isnan(f)?FP_NAN:
         __CPROVER_isinf(f)?FP_INFINITE:
         f==0?FP_ZERO:
         __CPROVER_isnormal(f)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: __fpclassifyl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyl(long double f) {
  __CPROVER_HIDE:
  return __CPROVER_isnan(f)?FP_NAN:
         __CPROVER_isinf(f)?FP_INFINITE:
         f==0?FP_ZERO:
         __CPROVER_isnormal(f)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: __fpclassify */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// The variant with long double below is needed for older Macs
// only; newer ones use __fpclassifyd.

inline int __fpclassify(
#ifdef __APPLE__
    long double d
#else
    double d
#endif
    ) {
  __CPROVER_HIDE:
  return __CPROVER_isnan(d)?FP_NAN:
         __CPROVER_isinf(d)?FP_INFINITE:
         d==0?FP_ZERO:
         __CPROVER_isnormal(d)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: sin */

double sin(double x)
{
  // gross over-approximation
  double ret;

  if(__CPROVER_isinf(x) || __CPROVER_isnan(x))
    __CPROVER_assume(__CPROVER_isnan(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==0);
  }

  return ret;
}

/* FUNCTION: sinl */

long double sinl(long double x)
{
  // gross over-approximation
  long double ret;

  if(__CPROVER_isinf(x) || __CPROVER_isnan(x))
    __CPROVER_assume(__CPROVER_isnan(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==0);
  }

  return ret;
}

/* FUNCTION: sinf */

float sinf(float x)
{
  // gross over-approximation
  float ret;

  if(__CPROVER_isinf(x) || __CPROVER_isnan(x))
    __CPROVER_assume(__CPROVER_isnan(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==0);
  }

  return ret;
}

/* FUNCTION: cos */

double cos(double x)
{
  // gross over-approximation
  double ret;

  if(__CPROVER_isinf(x) || __CPROVER_isnan(x))
    __CPROVER_assume(__CPROVER_isnan(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==1);
  }

  return ret;
}

/* FUNCTION: cosl */

long double cosl(long double x)
{
  // gross over-approximation
  long double ret;

  if(__CPROVER_isinf(x) || __CPROVER_isnan(x))
    __CPROVER_assume(__CPROVER_isnan(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==1);
  }

  return ret;
}

/* FUNCTION: cosf */

float cosf(float x)
{
__CPROVER_hide:;
  // gross over-approximation
  float ret;

  if(__CPROVER_isinf(x) || __CPROVER_isnan(x))
    __CPROVER_assume(__CPROVER_isnan(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==1);
  }

  return ret;
}

/* FUNCTION: __builtin_nan */

double __builtin_nan(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  (void)*str;
  return 0.0/0.0;
}

/* FUNCTION: __builtin_nanf */

float __builtin_nanf(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  (void)*str;
  return 0.0/0.0;
}

/* FUNCTION: nextUpf */

// IEEE_754 2008 althought similar to C's nextafter / nexttowards
// Assumes that float is (IEEE-754) binary32

union mixf
{
  float f;
  __CPROVER_bitvector[32] bv;
};

float nextUpf(float f)
{
__CPROVER_hide:;
  if (__CPROVER_isnan(f))
    return 0.0f/0.0f;  // NaN
  else if (f == 0.0f)
    return 0x1p-149f;
  else if (f > 0.0f)
  {
    if (__CPROVER_isinf(f))
      return f;

    union mixf m;
    m.f = f;
    ++m.bv;
    return m.f;
  }
  else
  {
    assert(f < 0.0f);

    union mixf m;
    m.f = f;
    --m.bv;
    return m.f;
  }
}

/* FUNCTION: nextUp */

// IEEE_754 2008 althought similar to C's nextafter / nexttowards
// Assumes that double is (IEEE-754) binary64

union mixd
{
  double f;
  __CPROVER_bitvector[64] bv;
};

double nextUp(double d)
{
__CPROVER_hide:;
  if (__CPROVER_isnan(d))
    return 0.0/0.0;  // NaN
  else if (d == 0.0)
    return 0x1.0p-1074;
  else if (d > 0.0)
  {
    if (__CPROVER_isinf(d))
      return d;

    union mixd m;
    m.f = d;
    ++m.bv;
    return m.f;
  }
  else
  {
    assert(d < 0.0);

    union mixd m;
    m.f = d;
    --m.bv;
    return m.f;
  }
}


/* Not nextUpl  as there is no obvious choice for the bit width of a
   long double.*/


/* FUNCTION: sqrtf */

/* This code is *WRONG* in some circumstances, specifically:
 *
 *   1. If run with a rounding mode other than RNE the
 *      answer will be out by one or two ULP.  This could be fixed
 *      with careful choice of round mode for the multiplications.
 *
 *   2. Subnormals have the unusual property that there are
 *      multiple numbers that square to give them.  I.E. if
 *      f is subnormal then there are multiple f1 != f2 such that
 *      f1 * f1 == f == f2 * f2.  This code will return *a*
 *      square root of a subnormal input but not necessarily *the*
 *      square root (i.e. the real value of the square root rounded).
 */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif



float nextUpf(float f);

float sqrtf(float f)
{
 __CPROVER_hide:;

  if ( f < 0.0f )
    return 0.0f/0.0f; // NaN
  else if (__CPROVER_isinf(f) ||   // +Inf only
	   f == 0.0f          ||   // Includes -0
	   __CPROVER_isnan(f))
    return f;
  else if (__CPROVER_isnormal(f))
  {
    float lower;    // Intentionally non-deterministic
    __CPROVER_assume(lower > 0);
    __CPROVER_assume(__CPROVER_isnormal(lower));
    // Tighter bounds can be given but are dependent on the
    // number of exponent and significand bits.  Thus they are
    // given implicitly...

    float lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormal(lowerSquare));

    float upper = nextUpf(lower);
    float upperSquare = upper * upper;  // Might be +Inf

    // Restrict these to bound f and thus compute the possible
    // values for the square root.  Note that the lower bound 
    // can be equal, this is important to catch edge cases such as
    // 0x1.fffffep+127f and relies on the smallest normal number
    // being a perfect square (which it will be for any sensible
    // bit width).
    __CPROVER_assume(lowerSquare <= f);
    __CPROVER_assume(f < upperSquare);

    // Select between them to work out which to return
    switch(__CPROVER_rounding_mode)
    {
    case FE_TONEAREST :
      return (f - lowerSquare < upperSquare - f) ? lower : upper; break;
    case FE_UPWARD :
      return (f - lowerSquare == 0.0f) ? lower : upper; break;
    case FE_DOWNWARD : // Fall through
    case FE_TOWARDZERO :
      return (f - lowerSquare == 0.0f) ? lower : upper; break;
    default :
      assert(0);
    }

  }
  else
  {
    assert(fpclassify(f) == FP_SUBNORMAL);
    assert(f > 0.0f);

    // With respect to the algebra of floating point number
    // all subnormals seem to be perfect squares, thus ...

    float root;    // Intentionally non-deterministic
    __CPROVER_assume(root >= 0.0f);

    __CPROVER_assume(root * root == f);

    return root;
  }
}




/* FUNCTION: sqrt */

/* The same caveats as sqrtf apply */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif



double nextUp (double d);

double sqrt(double d)
{
 __CPROVER_hide:;

  if ( d < 0.0f )
    return 0.0f/0.0f; // NaN
  else if (__CPROVER_isinf(d) ||   // +Inf only
	   d == 0.0f          ||   // Includes -0
	   __CPROVER_isnan(d))
    return d;
  else if (__CPROVER_isnormal(d))
  {
    double lower;    // Intentionally non-deterministic
    __CPROVER_assume(lower > 0);
    __CPROVER_assume(__CPROVER_isnormal(lower));

    double lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormal(lowerSquare));

    double upper = nextUp(lower);
    double upperSquare = upper * upper;  // Might be +Inf

    __CPROVER_assume(lowerSquare <= d);
    __CPROVER_assume(d < upperSquare);

    switch(__CPROVER_rounding_mode)
    {
    case FE_TONEAREST :
      return (d - lowerSquare < upperSquare - d) ? lower : upper; break;
    case FE_UPWARD :
      return (d - lowerSquare == 0.0f) ? lower : upper; break;
    case FE_DOWNWARD : // Fall through
    case FE_TOWARDZERO :
      return (d - lowerSquare == 0.0f) ? lower : upper; break;
    default :
      assert(0);
    }

  }
  else
  {
    assert(fpclassify(d) == FP_SUBNORMAL);
    assert(d > 0.0f);

    double root;    // Intentionally non-deterministic
    __CPROVER_assume(root >= 0.0f);

    __CPROVER_assume(root * root == d);

    return root;
  }
}

/* No sqrtl as no nextUpl */

