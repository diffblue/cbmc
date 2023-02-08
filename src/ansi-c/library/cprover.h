/*******************************************************************\

Module: C library check

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_LIBRARY_CPROVER_H
#define CPROVER_ANSI_C_LIBRARY_CPROVER_H

/// \file
/// CPROVER built-in declarations to perform library checks. This file is only
/// used by library_check.sh.

// NOLINTNEXTLINE(readability/identifiers)
typedef __typeof__(sizeof(int)) __CPROVER_size_t;
// NOLINTNEXTLINE(readability/identifiers)
typedef signed long long __CPROVER_ssize_t;

#define __CPROVER_constant_infinity_uint 1

void *__CPROVER_allocate(__CPROVER_size_t size, __CPROVER_bool zero);
void __CPROVER_deallocate(void *);
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_memory_leak;

extern int __CPROVER_malloc_failure_mode;
extern __CPROVER_size_t __CPROVER_max_malloc_size;
extern __CPROVER_bool __CPROVER_malloc_may_fail;

// malloc failure modes
extern int __CPROVER_malloc_failure_mode_return_null;
extern int __CPROVER_malloc_failure_mode_assert_then_assume;

struct __CPROVER_pipet {
  _Bool widowed;
  char data[4];
  short next_avail;
  short next_unread;
};

// __CPROVER_equal expects two arguments of the same type -- any type is
// permitted, unsigned long long is just used for the benefit of running syntax
// checks using system compilers
__CPROVER_bool __CPROVER_equal(unsigned long long, unsigned long long);

// The following built-ins are type checked by our C front-end and do not
// require declarations. They work with any types as described below. unsigned
// long long is just used to enable checks using system compilers.

// detect overflow
// the following expect two numeric arguments
__CPROVER_bool __CPROVER_overflow_minus(unsigned long long, unsigned long long);
__CPROVER_bool __CPROVER_overflow_mult(unsigned long long, unsigned long long);
__CPROVER_bool __CPROVER_overflow_plus(unsigned long long, unsigned long long);
__CPROVER_bool __CPROVER_overflow_shl(unsigned long long, unsigned long long);
// expects one numeric argument
__CPROVER_bool __CPROVER_overflow_unary_minus(unsigned long long);

// enumerations
// expects one enum-typed argument
__CPROVER_bool __CPROVER_enum_is_in_range(unsigned long long);

// The following have an optional second parameter (the width), and are
// polymorphic in the first parameter: if the second argument is omitted, then
// the width of the subtype of the pointer-typed first argument is used.
__CPROVER_bool __CPROVER_r_ok(const void *, ...);
__CPROVER_bool __CPROVER_w_ok(const void *, ...);
__CPROVER_bool __CPROVER_rw_ok(const void *, ...);

#include "../cprover_builtin_headers.h"

#endif // CPROVER_ANSI_C_LIBRARY_CPROVER_H
