/* FUNCTION: sem_init */

#include <semaphore.h>

int sem_init(sem_t *sem, int pshared, unsigned int value)
{
  __CPROVER_HIDE:;
  (void)pshared;
  (void)value;
  (void)sem;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(sem, "sem-init");
  __CPROVER_clear_may(sem, "sem-destroyed");
  #endif

  return 0;
}

/* FUNCTION: sem_wait */

#include <semaphore.h>

int sem_wait(sem_t *sem)
{
  __CPROVER_HIDE:;
  (void)sem;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  #endif

  return 0;
}

/* FUNCTION: sem_timedwait */

#include <semaphore.h>

int sem_timedwait(sem_t *sem, const struct timespec *abstime)
{
  __CPROVER_HIDE:;
  (void)sem;
  (void)abstime;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  #endif

  return 0;
}

/* FUNCTION: sem_trywait */

#include <semaphore.h>

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int sem_trywait(sem_t *sem)
{
  __CPROVER_HIDE:;
  (void)sem;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  #endif

  // POSIX.1-2017 sem_trywait(): the call may succeed (return 0) or fail
  // with EAGAIN (return -1, errno=EAGAIN) when the semaphore is already
  // locked.  Nondeterministic choice is a sound over-approximation.
  int result = __VERIFIER_nondet_int();
  if(result)
  {
    errno = EAGAIN;
    return -1;
  }
  return 0;
}

/* FUNCTION: sem_post */

#include <semaphore.h>

int sem_post(sem_t *sem)
{
  __CPROVER_HIDE:;
  (void)sem;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  #endif

  return 0;
}

/* FUNCTION: sem_post_multiple */

#include <semaphore.h>

int sem_post_multiple(sem_t *sem, int number)
{
  __CPROVER_HIDE:;
  (void)sem;
  (void)number;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  #endif

  return 0;
}

/* FUNCTION: sem_getvalue */

#include <semaphore.h>

int sem_getvalue(sem_t *sem, int *sval)
{
  __CPROVER_HIDE:;
  (void)sem;
  (void)sval;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  #endif

  return 0;
}

/* FUNCTION: sem_destroy */

#include <semaphore.h>

int sem_destroy(sem_t *sem)
{
  __CPROVER_HIDE:;
  (void)sem;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(sem, "sem-init"),
                   "semaphore must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(sem, "sem-destroyed"),
                   "semaphore must not be destroyed");
  __CPROVER_set_may(sem, "sem-destroyed");
  #endif

  return 0;
}
