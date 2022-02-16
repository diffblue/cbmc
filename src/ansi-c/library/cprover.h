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

void *__CPROVER_allocate(__CPROVER_size_t size, __CPROVER_bool zero);
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_new_object;
extern __CPROVER_bool __CPROVER_malloc_is_new_array;
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

#include "../cprover_builtin_headers.h"

#endif // CPROVER_ANSI_C_LIBRARY_CPROVER_H
