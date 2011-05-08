/* FUNCTION: pthread_mutex_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_init(
  pthread_mutex_t *mutex, const pthread_mutexattr_t *mutexattr)
{ __CPROVER_HIDE: *((char *)mutex)=0; return 0; }

/* FUNCTION: pthread_mutex_lock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_lock(pthread_mutex_t *mutex)
{ __CPROVER_HIDE:
  __CPROVER_atomic_begin();
  __CPROVER_assume(!*((char *)mutex));
  *((char *)mutex)=1;
  __CPROVER_atomic_end();
  return 0; // we never fail
}

/* FUNCTION: pthread_mutex_trylock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_trylock(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:
  __CPROVER_atomic_begin();
  if(*((char *)mutex)) { __CPROVER_atomic_end(); return 1; }
  *((char *)mutex)=1;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_mutex_unlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_unlock(pthread_mutex_t *mutex)
{ __CPROVER_HIDE:
  __CPROVER_assert(*((char *)mutex),
    "must hold lock upon unlock");
  *((char *)mutex)=0;
  return 0; // we never fail
}

/* FUNCTION: pthread_mutex_destroy */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_destroy(pthread_mutex_t *mutex)
{ }

/* FUNCTION: pthread_exit */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline void pthread_exit(void *value_ptr)
{ __CPROVER_hide:; __CPROVER_assume(0); }

/* FUNCTION: pthread_rwlock_destroy */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_destroy(pthread_rwlock_t *lock)
{ }

/* FUNCTION: pthread_rwlock_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_init(pthread_rwlock_t *lock, 
  const pthread_rwlockattr_t *attr)
{ __CPROVER_HIDE: (*(char *)lock)=0; }

/* FUNCTION: pthread_rwlock_rdlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_rdlock(pthread_rwlock_t *lock)
{ /* TODO */ }

/* FUNCTION: pthread_rwlock_tryrdlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_tryrdlock(pthread_rwlock_t *lock)
{ /* TODO */ }

/* FUNCTION: pthread_rwlock_trywrlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_trywrlock(pthread_rwlock_t *lock)
{ __CPROVER_HIDE:
  __CPROVER_atomic_begin();
  if(*(char *)lock) { __CPROVER_atomic_end(); return 1; }
  (*(char *)lock)=1;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_rwlock_unlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_unlock(pthread_rwlock_t *lock)
{ __CPROVER_HIDE: (*(char *)lock)=0; }

/* FUNCTION: pthread_rwlock_wrlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_wrlock(pthread_rwlock_t *lock)
{ __CPROVER_HIDE:
  __CPROVER_atomic_begin();
  __CPROVER_assume(!(*(char *)lock));
  (*(char *)lock)=1;
  __CPROVER_atomic_end();
  return 0; // we never fail
}

/* FUNCTION: pthread_create */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_create(
  pthread_t *thread,
  pthread_attr_t *attr,
  void * (*start_routine)(void *),
  void *arg)
{
  __CPROVER_HIDE:;
  pthread_t thread_id;

  if(!thread) *thread=thread_id;
  __CPROVER_ASYNC_1: start_routine(arg);

  return 0;
}

