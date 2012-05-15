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

/* FUNCTION: isinf */

inline int isinf(double d) { return __CPROVER_isinf(d); }

/* FUNCTION: isnan */

inline int isnan(double d) { return __CPROVER_isnan(d); }

/* FUNCTION: __isnanf */

inline int __isnanf(float f) { return __CPROVER_isnan(f); }

/* FUNCTION: isnormal */

int isnormal(double d) { return __CPROVER_isnormal(d); }

/* FUNCTION: __builtin_inff */

float __builtin_inff(void) { return __CPROVER_inff(); }

/* FUNCTION: __builtin_inf */

double __builtin_inf(void) { return __CPROVER_inf(); }

/* FUNCTION: signbit */

inline int signbit(double d) { return __CPROVER_sign(d); }

/* FUNCTION: __signbitf */

inline float __signbitf(float f) { return __CPROVER_sign(f); }

/* FUNCTION: __signbit */

inline double __signbit(double d) { return __CPROVER_sign(d); }

/* FUNCTION: __fpclassifyd */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyd(double d) {
  if(__CPROVER_isnan(d)) return FP_NAN;
  if(__CPROVER_isinf(d)) return FP_INFINITE;
  if(d==0) return FP_ZERO;
  if(__CPROVER_isnormal(d)) return FP_NORMAL;
  return FP_SUBNORMAL;
}

/* FUNCTION: __fpclassifyf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyf(float f) {
  if(__CPROVER_isnan(f)) return FP_NAN;
  if(__CPROVER_isinf(f)) return FP_INFINITE;
  if(f==0) return FP_ZERO;
  if(__CPROVER_isnormal(f)) return FP_NORMAL;
  return FP_SUBNORMAL;
}

/* FUNCTION: __fpclassify */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassify(long double d) {
  if(__CPROVER_isnan(d)) return FP_NAN;
  if(__CPROVER_isinf(d)) return FP_INFINITE;
  if(d==0) return FP_ZERO;
  if(__CPROVER_isnormal(d)) return FP_NORMAL;
  return FP_SUBNORMAL;
}
