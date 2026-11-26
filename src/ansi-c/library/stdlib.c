/* FUNCTION: abs */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

#undef abs

int abs(int i)
{
  // C99 Section 7.20.6.1:
  // "If the result cannot be represented, the behavior is undefined."
  __CPROVER_precondition(i != INT_MIN, "argument to abs must not be INT_MIN");
  return __CPROVER_abs(i);
}

/* FUNCTION: labs */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

#undef labs

long int labs(long int i)
{
  // C99 Section 7.20.6.1:
  // "If the result cannot be represented, the behavior is undefined."
  __CPROVER_precondition(
    i != LONG_MIN, "argument to labs must not be LONG_MIN");
  return __CPROVER_labs(i);
}

/* FUNCTION: llabs */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

#undef llabs

long long int llabs(long long int i)
{
  // C99 Section 7.20.6.1:
  // "If the result cannot be represented, the behavior is undefined."
  __CPROVER_precondition(
    i != LLONG_MIN, "argument to llabs must not be LLONG_MIN");
  return __CPROVER_llabs(i);
}

/* FUNCTION: imaxabs */

#ifndef __CPROVER_INTTYPES_H_INCLUDED
#  include <inttypes.h>
#  define __CPROVER_INTTYPES_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

#undef imaxabs

intmax_t __CPROVER_imaxabs(intmax_t);

intmax_t imaxabs(intmax_t i)
{
  __CPROVER_precondition(
    i != INTMAX_MIN, "argument to imaxabs must not be INTMAX_MIN");
  return __CPROVER_imaxabs(i);
}

/* FUNCTION: __builtin_abs */

int __builtin_abs(int i)
{
  return __CPROVER_abs(i);
}

/* FUNCTION: __builtin_labs */

long int __builtin_labs(long int i)
{
  return __CPROVER_labs(i);
}

/* FUNCTION: __builtin_llabs */

long long int __builtin_llabs(long long int i)
{
  return __CPROVER_llabs(i);
}

/* FUNCTION: exit */

#undef exit

void exit(int status)
{
  (void)status;
  __CPROVER_assume(0);
#ifdef LIBRARY_CHECK
  __builtin_unreachable();
#endif
}

/* FUNCTION: __builtin_exit */

void __builtin_exit(int status)
{
  (void)status;
  __CPROVER_assume(0);
}

/* FUNCTION: _Exit */

#undef _Exit

void _Exit(int status)
{
  (void)status;
  __CPROVER_assume(0);
#ifdef LIBRARY_CHECK
  __builtin_unreachable();
#endif
}

/* FUNCTION: abort */

#undef abort

void abort(void)
{
  __CPROVER_assume(0);
#ifdef LIBRARY_CHECK
  __builtin_unreachable();
#endif
}

/* FUNCTION: calloc */

#undef calloc

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
#ifndef __GNUC__
_Bool __builtin_mul_overflow();
#endif
__CPROVER_bool __CPROVER_malloc_is_new_array;

void *calloc(__CPROVER_size_t nmemb, __CPROVER_size_t size)
{
__CPROVER_HIDE:;
  __CPROVER_size_t alloc_size;
  if(__builtin_mul_overflow(nmemb, size, &alloc_size))
    return (void *)0;

  if(__CPROVER_malloc_failure_mode == __CPROVER_malloc_failure_mode_return_null)
  {
    __CPROVER_bool should_malloc_fail = __VERIFIER_nondet___CPROVER_bool();
    if(
      alloc_size > __CPROVER_max_malloc_size ||
      (__CPROVER_malloc_may_fail && should_malloc_fail))
    {
      return (void *)0;
    }
  }
  else if(
    __CPROVER_malloc_failure_mode ==
    __CPROVER_malloc_failure_mode_assert_then_assume)
  {
    __CPROVER_assert(
      alloc_size <= __CPROVER_max_malloc_size, "max allocation size exceeded");
    __CPROVER_assume(alloc_size <= __CPROVER_max_malloc_size);

    __CPROVER_bool should_malloc_fail = __VERIFIER_nondet___CPROVER_bool();
    __CPROVER_assert(
      !__CPROVER_malloc_may_fail || !should_malloc_fail,
      "max allocation may fail");
    __CPROVER_assume(!__CPROVER_malloc_may_fail || !should_malloc_fail);
  }

  void *malloc_res;
  // realistically, calloc may return NULL,
  // and __CPROVER_allocate doesn't, but no one cares
  malloc_res = __CPROVER_allocate(alloc_size, 1);

  // record the object size for non-determistic bounds checking
  __CPROVER_bool record_malloc = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_is_new_array =
    record_malloc ? 0 : __CPROVER_malloc_is_new_array;

  // detect memory leaks
  __CPROVER_bool record_may_leak = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_memory_leak = record_may_leak ? malloc_res : __CPROVER_memory_leak;

#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assume(__CPROVER_buffer_size(malloc_res) == alloc_size);
  __CPROVER_is_zero_string(malloc_res) = 1;
  __CPROVER_zero_string_length(malloc_res) = 0;
#endif

  return malloc_res;
}

/* FUNCTION: malloc */

#undef malloc

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
#ifndef LIBRARY_CHECK
__CPROVER_bool __CPROVER_malloc_is_new_array;
#endif

// malloc is marked "inline" for the benefit of goto-analyzer. Really,
// goto-analyzer should take care of inlining as needed.
inline void *malloc(__CPROVER_size_t malloc_size)
{
// realistically, malloc may return NULL,
// but we only do so if `--malloc-may-fail` is set
__CPROVER_HIDE:;

  if(__CPROVER_malloc_failure_mode == __CPROVER_malloc_failure_mode_return_null)
  {
    __CPROVER_bool should_malloc_fail = __VERIFIER_nondet___CPROVER_bool();
    if(
      malloc_size > __CPROVER_max_malloc_size ||
      (__CPROVER_malloc_may_fail && should_malloc_fail))
    {
      return (void *)0;
    }
  }
  else if(
    __CPROVER_malloc_failure_mode ==
    __CPROVER_malloc_failure_mode_assert_then_assume)
  {
    __CPROVER_assert(
      malloc_size <= __CPROVER_max_malloc_size, "max allocation size exceeded");
    __CPROVER_assume(malloc_size <= __CPROVER_max_malloc_size);

    __CPROVER_bool should_malloc_fail = __VERIFIER_nondet___CPROVER_bool();
    __CPROVER_assert(
      !__CPROVER_malloc_may_fail || !should_malloc_fail,
      "max allocation may fail");
    __CPROVER_assume(!__CPROVER_malloc_may_fail || !should_malloc_fail);
  }

  void *malloc_res;
  malloc_res = __CPROVER_allocate(malloc_size, 0);

  // record the object size for non-determistic bounds checking
  __CPROVER_bool record_malloc = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_is_new_array =
    record_malloc ? 0 : __CPROVER_malloc_is_new_array;

  // detect memory leaks
  __CPROVER_bool record_may_leak = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_memory_leak = record_may_leak ? malloc_res : __CPROVER_memory_leak;

#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assume(__CPROVER_buffer_size(malloc_res) == malloc_size);
#endif

  return malloc_res;
}

/* FUNCTION: __builtin_alloca */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
const void *__CPROVER_alloca_object;
#ifndef LIBRARY_CHECK
__CPROVER_bool __CPROVER_malloc_is_new_array;
#endif

void *__builtin_alloca(__CPROVER_size_t alloca_size)
{
  __CPROVER_HIDE:;
  void *res;
  res = __CPROVER_allocate(alloca_size, 0);

  // record the object size for non-determistic bounds checking
  __CPROVER_bool record_malloc=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;

  // record alloca to detect invalid free
  __CPROVER_bool record_alloca = __VERIFIER_nondet___CPROVER_bool();
  __CPROVER_alloca_object = record_alloca ? res : __CPROVER_alloca_object;

#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assume(__CPROVER_buffer_size(res) == alloca_size);
#endif

  return res;
}

/* FUNCTION: alloca */

#undef alloca

void *__builtin_alloca(__CPROVER_size_t alloca_size);

void *alloca(__CPROVER_size_t alloca_size)
{
__CPROVER_HIDE:;
  return __builtin_alloca(alloca_size);
}

/* FUNCTION: free */

#undef free

void __CPROVER_deallocate(void *);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
#ifndef LIBRARY_CHECK
const void *__CPROVER_alloca_object;
#endif
const void *__CPROVER_new_object;
#ifndef LIBRARY_CHECK
__CPROVER_bool __CPROVER_malloc_is_new_array;
#endif

void free(void *ptr)
{
  __CPROVER_HIDE:;
  // If ptr is NULL, no operation is performed.
  __CPROVER_precondition(
    ptr == 0 || __CPROVER_r_ok(ptr, 0),
    "free argument must be NULL or valid pointer");
  __CPROVER_precondition(ptr==0 || __CPROVER_DYNAMIC_OBJECT(ptr),
                         "free argument must be dynamic object");
  __CPROVER_precondition(ptr==0 || __CPROVER_POINTER_OFFSET(ptr)==0,
                         "free argument has offset zero");

  // catch double free
  __CPROVER_precondition(ptr==0 || __CPROVER_deallocated!=ptr,
                         "double free");

  // catch people who try to use free(...) for stuff
  // allocated with new[]
  __CPROVER_precondition(
    ptr == 0 || __CPROVER_new_object != ptr || !__CPROVER_malloc_is_new_array,
    "free called for new[] object");

  // catch people who try to use free(...) with alloca
  __CPROVER_precondition(
    ptr == 0 || __CPROVER_alloca_object != ptr,
    "free called for stack-allocated object");

  if(ptr!=0)
  {
    __CPROVER_deallocate(ptr);

    // detect memory leaks
    if(__CPROVER_memory_leak==ptr)
      __CPROVER_memory_leak=0;
  }
}

/* FUNCTION: __CPROVER_strto_scan */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

#undef isspace

int isspace(int);

#ifndef __GNUC__
_Bool __builtin_add_overflow();
_Bool __builtin_mul_overflow();
#endif

// The value of the digit ch in bases up to 36, and 36 for any other character
#define __CPROVER_STRTO_DIGIT_VALUE(ch)                                        \
  ((ch) >= '0' && (ch) <= '9'   ? (ch) - '0'                                   \
   : (ch) >= 'a' && (ch) <= 'z' ? (ch) - 'a' + 10                              \
   : (ch) >= 'A' && (ch) <= 'Z' ? (ch) - 'A' + 10                              \
                                : 36)

/// Scan an integer as specified for strtol, strtoll, strtoul, and strtoull
/// in C23 7.24.1.7, and set \p *endptr (if \p endptr is not null).
/// \param nptr: the string to convert
/// \param endptr: where to store the end of the subject sequence
/// \param base: the base, or 0 to determine the base from the prefix
/// \param c23: whether to accept a "0b" or "0B" prefix for base 0 and 2, as
///   C23 does
/// \param [out] negative: whether the subject sequence starts with '-'
/// \param [out] overflow: whether the magnitude exceeds ULLONG_MAX
/// \return the magnitude of the converted value, or ULLONG_MAX if \p overflow
///   is set; 0 (with \p negative and \p overflow false) if no conversion
///   could be performed
unsigned long long __CPROVER_strto_scan(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23,
  _Bool *negative,
  _Bool *overflow)
{
__CPROVER_HIDE:;
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(
    __CPROVER_is_zero_string(nptr), "zero-termination of argument of strto*");
#endif

  *negative = 0;
  *overflow = 0;

  if(base == 1 || base < 0 || base > 36)
  {
    errno = EINVAL;
    return 0;
  }

  __CPROVER_size_t i = 0;
  while(isspace((unsigned char)nptr[i]))
    ++i;

  _Bool is_negative = 0;
  if(nptr[i] == '-')
  {
    is_negative = 1;
    ++i;
  }
  else if(nptr[i] == '+')
    ++i;

  // A prefix is only part of the subject sequence if a digit follows it.
  if(
    (base == 0 || base == 16) && nptr[i] == '0' &&
    (nptr[i + 1] == 'x' || nptr[i + 1] == 'X') &&
    __CPROVER_STRTO_DIGIT_VALUE(nptr[i + 2]) < 16)
  {
    base = 16;
    i += 2;
  }
  else if(
    c23 && (base == 0 || base == 2) && nptr[i] == '0' &&
    (nptr[i + 1] == 'b' || nptr[i + 1] == 'B') &&
    __CPROVER_STRTO_DIGIT_VALUE(nptr[i + 2]) < 2)
  {
    base = 2;
    i += 2;
  }
  else if(base == 0)
    base = nptr[i] == '0' ? 8 : 10;

  const __CPROVER_size_t first_digit = i;
  unsigned long long result = 0;
  _Bool has_overflow = 0;
  for(;; ++i)
  {
    int digit = __CPROVER_STRTO_DIGIT_VALUE(nptr[i]);
    if(digit >= base)
      break;
    // keep consuming digits after an overflow, as endptr must point past the
    // subject sequence
    if(
      !has_overflow &&
      (__builtin_mul_overflow(result, (unsigned long long)base, &result) ||
       __builtin_add_overflow(result, (unsigned long long)digit, &result)))
    {
      has_overflow = 1;
    }
  }

  if(i == first_digit)
  {
    // no conversion performed
    if(endptr != 0)
      *endptr = (char *)nptr;
    return 0;
  }

  if(endptr != 0)
    *endptr = (char *)nptr + i;

  *negative = is_negative;
  *overflow = has_overflow;
  return has_overflow ? ULLONG_MAX : result;
}

#undef __CPROVER_STRTO_DIGIT_VALUE

/* FUNCTION: __CPROVER_strtol_internal */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

unsigned long long __CPROVER_strto_scan(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23,
  _Bool *negative,
  _Bool *overflow);

/// Convert as strtol, accepting C23 prefixes if \p c23 is set.
long __CPROVER_strtol_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23)
{
__CPROVER_HIDE:;
  _Bool negative, overflow;
  unsigned long long magnitude =
    __CPROVER_strto_scan(nptr, endptr, base, c23, &negative, &overflow);

  if(negative)
  {
    if(overflow || magnitude > (unsigned long long)LONG_MAX + 1)
    {
      errno = ERANGE;
      return LONG_MIN;
    }
    return magnitude == (unsigned long long)LONG_MAX + 1 ? LONG_MIN
                                                         : -(long)magnitude;
  }
  else if(overflow || magnitude > LONG_MAX)
  {
    errno = ERANGE;
    return LONG_MAX;
  }
  else
    return (long)magnitude;
}

/* FUNCTION: strtol */

#undef strtol

long __CPROVER_strtol_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

long strtol(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtol_internal(nptr, endptr, base, 0);
}

/* FUNCTION: __isoc23_strtol */

long __CPROVER_strtol_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

// glibc 2.38 and later redirect strtol to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtol, it accepts the C23 "0b" prefix.
long __isoc23_strtol(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtol_internal(nptr, endptr, base, 1);
}

/* FUNCTION: __CPROVER_strtoll_internal */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

unsigned long long __CPROVER_strto_scan(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23,
  _Bool *negative,
  _Bool *overflow);

/// Convert as strtoll, accepting C23 prefixes if \p c23 is set.
long long
__CPROVER_strtoll_internal(const char *nptr, char **endptr, int base, _Bool c23)
{
__CPROVER_HIDE:;
  _Bool negative, overflow;
  unsigned long long magnitude =
    __CPROVER_strto_scan(nptr, endptr, base, c23, &negative, &overflow);

  if(negative)
  {
    if(overflow || magnitude > (unsigned long long)LLONG_MAX + 1)
    {
      errno = ERANGE;
      return LLONG_MIN;
    }
    return magnitude == (unsigned long long)LLONG_MAX + 1
             ? LLONG_MIN
             : -(long long)magnitude;
  }
  else if(overflow || magnitude > LLONG_MAX)
  {
    errno = ERANGE;
    return LLONG_MAX;
  }
  else
    return (long long)magnitude;
}

/* FUNCTION: strtoll */

#undef strtoll

long long __CPROVER_strtoll_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

long long strtoll(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtoll_internal(nptr, endptr, base, 0);
}

/* FUNCTION: __isoc23_strtoll */

long long __CPROVER_strtoll_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

// glibc 2.38 and later redirect strtoll to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtoll, it accepts the C23 "0b" prefix.
long long __isoc23_strtoll(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtoll_internal(nptr, endptr, base, 1);
}

/* FUNCTION: __CPROVER_strtoul_internal */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

unsigned long long __CPROVER_strto_scan(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23,
  _Bool *negative,
  _Bool *overflow);

/// Convert as strtoul, accepting C23 prefixes if \p c23 is set.
unsigned long
__CPROVER_strtoul_internal(const char *nptr, char **endptr, int base, _Bool c23)
{
__CPROVER_HIDE:;
  _Bool negative, overflow;
  unsigned long long magnitude =
    __CPROVER_strto_scan(nptr, endptr, base, c23, &negative, &overflow);

  if(overflow || magnitude > ULONG_MAX)
  {
    errno = ERANGE;
    return ULONG_MAX;
  }

  // C23 7.24.1.7p5: a leading '-' negates the converted value in the return
  // type
  return negative ? -(unsigned long)magnitude : (unsigned long)magnitude;
}

/* FUNCTION: strtoul */

#undef strtoul

unsigned long __CPROVER_strtoul_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

unsigned long strtoul(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtoul_internal(nptr, endptr, base, 0);
}

/* FUNCTION: __isoc23_strtoul */

unsigned long __CPROVER_strtoul_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

// glibc 2.38 and later redirect strtoul to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtoul, it accepts the C23 "0b" prefix.
unsigned long __isoc23_strtoul(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtoul_internal(nptr, endptr, base, 1);
}

/* FUNCTION: __CPROVER_strtoull_internal */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

unsigned long long __CPROVER_strto_scan(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23,
  _Bool *negative,
  _Bool *overflow);

/// Convert as strtoull, accepting C23 prefixes if \p c23 is set.
unsigned long long __CPROVER_strtoull_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23)
{
__CPROVER_HIDE:;
  _Bool negative, overflow;
  unsigned long long magnitude =
    __CPROVER_strto_scan(nptr, endptr, base, c23, &negative, &overflow);

  if(overflow)
  {
    errno = ERANGE;
    return ULLONG_MAX;
  }

  // C23 7.24.1.7p5: a leading '-' negates the converted value in the return
  // type
  return negative ? -magnitude : magnitude;
}
/* FUNCTION: strtoull */

#undef strtoull

unsigned long long __CPROVER_strtoull_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

unsigned long long strtoull(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtoull_internal(nptr, endptr, base, 0);
}

/* FUNCTION: __isoc23_strtoull */

unsigned long long __CPROVER_strtoull_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

// glibc 2.38 and later redirect strtoull to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtoull, it accepts the C23 "0b" prefix.
unsigned long long __isoc23_strtoull(const char *nptr, char **endptr, int base)
{
__CPROVER_HIDE:;
  return __CPROVER_strtoull_internal(nptr, endptr, base, 1);
}

/* FUNCTION: strtol_l */

// POSIX.1-2024: as strtol, with a locale argument. The conversion of integers
// only depends on the locale via the white-space characters, which the model
// takes from the "C" locale. libc++ converts integers read by num_get with
// strtoll_l and strtoull_l.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

long __CPROVER_strtol_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

long strtol_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtol_internal(nptr, endptr, base, 0);
}

#endif

/* FUNCTION: __isoc23_strtol_l */

// glibc 2.38 and later redirect strtol_l to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtol_l, it accepts the C23 "0b" prefix.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

long __CPROVER_strtol_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

long __isoc23_strtol_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtol_internal(nptr, endptr, base, 1);
}

#endif

/* FUNCTION: strtoul_l */

// POSIX.1-2024: as strtoul, with a locale argument. The conversion of integers
// only depends on the locale via the white-space characters, which the model
// takes from the "C" locale. libc++ converts integers read by num_get with
// strtoll_l and strtoull_l.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

unsigned long __CPROVER_strtoul_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

unsigned long strtoul_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtoul_internal(nptr, endptr, base, 0);
}

#endif

/* FUNCTION: __isoc23_strtoul_l */

// glibc 2.38 and later redirect strtoul_l to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtoul_l, it accepts the C23 "0b" prefix.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

unsigned long __CPROVER_strtoul_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

unsigned long
__isoc23_strtoul_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtoul_internal(nptr, endptr, base, 1);
}

#endif

/* FUNCTION: strtoll_l */

// POSIX.1-2024: as strtoll, with a locale argument. The conversion of integers
// only depends on the locale via the white-space characters, which the model
// takes from the "C" locale. libc++ converts integers read by num_get with
// strtoll_l and strtoull_l.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

long long __CPROVER_strtoll_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

long long strtoll_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtoll_internal(nptr, endptr, base, 0);
}

#endif

/* FUNCTION: __isoc23_strtoll_l */

// glibc 2.38 and later redirect strtoll_l to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtoll_l, it accepts the C23 "0b" prefix.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

long long __CPROVER_strtoll_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

long long
__isoc23_strtoll_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtoll_internal(nptr, endptr, base, 1);
}

#endif

/* FUNCTION: strtoull_l */

// POSIX.1-2024: as strtoull, with a locale argument. The conversion of integers
// only depends on the locale via the white-space characters, which the model
// takes from the "C" locale. libc++ converts integers read by num_get with
// strtoll_l and strtoull_l.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

unsigned long long __CPROVER_strtoull_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

unsigned long long
strtoull_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtoull_internal(nptr, endptr, base, 0);
}

#endif

/* FUNCTION: __isoc23_strtoull_l */

// glibc 2.38 and later redirect strtoull_l to this function in C23 mode, with
// _GNU_SOURCE, and in C++. Unlike strtoull_l, it accepts the C23 "0b" prefix.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

unsigned long long __CPROVER_strtoull_internal(
  const char *nptr,
  char **endptr,
  int base,
  _Bool c23);

unsigned long long
__isoc23_strtoull_l(const char *nptr, char **endptr, int base, locale_t loc)
{
__CPROVER_HIDE:;
  (void)loc;
  return __CPROVER_strtoull_internal(nptr, endptr, base, 1);
}

#endif

/* FUNCTION: atoi */

#undef atoi
#undef strtol

long strtol(const char *nptr, char **endptr, int base);

int atoi(const char *nptr)
{
  __CPROVER_HIDE:;
  return (int)strtol(nptr, (char **)0, 10);
}

/* FUNCTION: atol */

#undef atol
#undef strtol

long strtol(const char *nptr, char **endptr, int base);

long atol(const char *nptr)
{
  __CPROVER_HIDE:;
  return strtol(nptr, (char **)0, 10);
}

/* FUNCTION: getenv */

#undef getenv

#ifndef __CPROVER_STDDEF_H_INCLUDED
#  include <stddef.h>
#  define __CPROVER_STDDEF_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
ptrdiff_t __VERIFIER_nondet_ptrdiff_t(void);

char *getenv(const char *name)
{
  __CPROVER_HIDE:;

  (void)*name;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(name),
    "zero-termination of argument of getenv");
  #endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "getenv_result");
  char *getenv_result;
  __CPROVER_set_must(getenv_result, "getenv_result");
  return getenv_result;

#else

  __CPROVER_bool found=__VERIFIER_nondet___CPROVER_bool();
  if(!found) return 0;

  ptrdiff_t buf_size = __VERIFIER_nondet_ptrdiff_t();

  // It's reasonable to assume this won't exceed the signed
  // range in practice, but in principle, this could exceed
  // the range.

  __CPROVER_assume(buf_size >= 1);
  char *buffer = (char *)__CPROVER_allocate(buf_size * sizeof(char), 0);
  buffer[buf_size-1]=0;

#  ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assume(__CPROVER_buffer_size(buffer) == buf_size);
  __CPROVER_is_zero_string(buffer) = 1;
  __CPROVER_zero_string_length(buffer) = buf_size - 1;
#  endif

  return buffer;
#endif
}

/* FUNCTION: realloc */

void *malloc(__CPROVER_size_t malloc_size);
void free(void *ptr);

void *realloc(void *ptr, __CPROVER_size_t malloc_size)
{
  __CPROVER_HIDE:;

  __CPROVER_precondition(ptr==0 || __CPROVER_DYNAMIC_OBJECT(ptr),
                         "realloc argument is dynamic object");

  // if ptr is NULL, this behaves like malloc
  if(ptr==0)
    return malloc(malloc_size);

  // if malloc-size is 0, allocate new minimum sized object
  // and free original
  if(malloc_size==0)
  {
    free(ptr);
    return malloc(0);
  }

  // this shouldn't move if the new size isn't bigger
  void *res;
  res=malloc(malloc_size);
  if(res != (void *)0)
  {
    __CPROVER_array_copy(res, ptr);
    free(ptr);
  }

  return res;
}

/* FUNCTION: valloc */

void *malloc(__CPROVER_size_t malloc_size);

void *valloc(__CPROVER_size_t malloc_size)
{
  // The allocated memory is aligned on a page
  // boundary, which we don't model.

  __CPROVER_HIDE:;
  return malloc(malloc_size);
}

/* FUNCTION: posix_memalign */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

#undef posix_memalign

void *malloc(__CPROVER_size_t malloc_size);
int posix_memalign(
  void **ptr,
  __CPROVER_size_t alignment,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;

  __CPROVER_size_t multiplier = alignment / sizeof(void *);
  // Modeling the posix_memalign checks on alignment.
  if(
    alignment % sizeof(void *) != 0 || ((multiplier) & (multiplier - 1)) != 0 ||
    alignment == 0)
  {
    return EINVAL;
  }
  // The address of the allocated memory is supposed to be aligned with
  // alignment. As cbmc doesn't model address alignment,
  // assuming MALLOC_ALIGNMENT = MAX_INT_VALUE seems fair.
  // As _mid_memalign simplifies for alignment <= MALLOC_ALIGNMENT
  // to a malloc call, it should be sound, if we do it too.

  void *tmp = malloc(size);
  if(tmp != (void *)0)
  {
    *ptr = tmp;
    return 0;
  }
  return ENOMEM;
}

/* FUNCTION: random */

long __VERIFIER_nondet_long(void);

long random(void)
{
  // We return a non-deterministic value instead of a random one.
  __CPROVER_HIDE:;
  long result=__VERIFIER_nondet_long();
  __CPROVER_assume(result>=0 && result<=2147483647);
  return result;
}

/* FUNCTION: rand */

int __VERIFIER_nondet_int(void);

int rand(void)
{
__CPROVER_HIDE:;
  // We return a non-deterministic value instead of a random one.
  int result = __VERIFIER_nondet_int();
  __CPROVER_assume(result >= 0);
  return result;
}

/* FUNCTION: rand_r */

int __VERIFIER_nondet_int(void);

int rand_r(unsigned int *seed)
{
__CPROVER_HIDE:;
  // We return a non-deterministic value instead of a random one.
  (void)*seed;
  int result = __VERIFIER_nondet_int();
  __CPROVER_assume(result >= 0);
  return result;
}

/* FUNCTION: __CPROVER_deallocate */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

void __CPROVER_deallocate(void *ptr)
{
  if(__VERIFIER_nondet___CPROVER_bool())
    __CPROVER_deallocated = ptr;
}
