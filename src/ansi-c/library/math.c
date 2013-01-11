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
  return 0.0/0.0;
}

/* FUNCTION: __builtin_nanf */

float __builtin_nanf(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  return 0.0/0.0;
}
