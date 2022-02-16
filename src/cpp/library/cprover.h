/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPP_LIBRARY_CPROVER_H
#define CPROVER_CPP_LIBRARY_CPROVER_H

// NOLINTNEXTLINE(readability/identifiers)
typedef __typeof__(sizeof(int)) __CPROVER_size_t;
void *__CPROVER_allocate(__CPROVER_size_t size, __CPROVER_bool zero);
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_new_object;
extern _Bool __CPROVER_malloc_is_new_array;
extern const void *__CPROVER_memory_leak;

void __CPROVER_assume(__CPROVER_bool assumption) __attribute__((__noreturn__));
void __CPROVER_assert(__CPROVER_bool assertion, const char *description);
void __CPROVER_precondition(__CPROVER_bool assertion, const char *description);
void __CPROVER_postcondition(__CPROVER_bool assertion, const char *description);

void __CPROVER_input(const char *description, ...);
void __CPROVER_output(const char *description, ...);

// concurrency-related
void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();
void __CPROVER_fence(const char *kind, ...);

// pointers
unsigned __CPROVER_POINTER_OBJECT(const void *p);
signed __CPROVER_POINTER_OFFSET(const void *p);
__CPROVER_bool __CPROVER_DYNAMIC_OBJECT(const void *p);

// arrays
// __CPROVER_bool __CPROVER_array_equal(const void *array1, const void *array2);
void __CPROVER_array_copy(const void *dest, const void *src);
void __CPROVER_array_set(const void *dest, ...);
void __CPROVER_array_replace(const void *dest, const void *src);

void __CPROVER_set_must(const void *, const char *);
void __CPROVER_set_may(const void *, const char *);
void __CPROVER_clear_must(const void *, const char *);
void __CPROVER_clear_may(const void *, const char *);
void __CPROVER_cleanup(const void *, void (*)(void *));
__CPROVER_bool __CPROVER_get_must(const void *, const char *);
__CPROVER_bool __CPROVER_get_may(const void *, const char *);

#endif // CPROVER_CPP_LIBRARY_CPROVER_H
