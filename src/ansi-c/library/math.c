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

/* FUNCTION: isnan */

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

float __builtin_inff(void) { return __CPROVER_inff(); }

/* FUNCTION: __builtin_inf */

double __builtin_inf(void) { return __CPROVER_inf(); }

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
