/* FUNCTION: pthread_mutex_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_init(
  pthread_mutex_t *mutex, const pthread_mutexattr_t *mutexattr)
{
  __CPROVER_HIDE:;
  *((signed char *)mutex)=0;
  if(mutexattr!=0) (void)*mutexattr;
  return 0;
}

/* FUNCTION: pthread_mutex_lock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_lock(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  __CPROVER_assert(*((signed char *)mutex)!=-1,
    "mutex not initialised or destroyed");
  __CPROVER_assume(!*((signed char *)mutex));
  *((signed char *)mutex)=1;
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
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  __CPROVER_assert(*((signed char *)mutex)!=-1,
    "mutex not initialised or destroyed");
  if(*((signed char *)mutex)==1) { __CPROVER_atomic_end(); return 1; }
  *((signed char *)mutex)=1;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_mutex_unlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_unlock(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(*((signed char *)mutex)==1,
    "must hold lock upon unlock");
  *((signed char *)mutex)=0;
  return 0; // we never fail
}

/* FUNCTION: pthread_mutex_destroy */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutex_destroy(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(*((signed char *)mutex)==0,
    "lock held upon destroy");
  *((signed char *)mutex)=-1;
  return 0;
}

/* FUNCTION: pthread_exit */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

extern unsigned long long __CPROVER_threads_exited;
extern _Thread_local unsigned long __CPROVER_thread_id;

inline void pthread_exit(void *value_ptr)
{
  __CPROVER_HIDE:;
  if(value_ptr!=0) (void)*(char*)value_ptr;
  __CPROVER_threads_exited|=1<<__CPROVER_thread_id;
  __CPROVER_assume(0);
}

/* FUNCTION: pthread_join */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

extern unsigned long long __CPROVER_threads_exited;

inline int pthread_join(pthread_t thread, void **value_ptr)
{
  __CPROVER_HIDE:;
  if(value_ptr!=0) (void)**(char**)value_ptr;
#ifdef __APPLE__
  if((unsigned long)(thread->__sig)<8*sizeof(unsigned long long))
    __CPROVER_assume(__CPROVER_threads_exited&(1<<(unsigned long)thread->__sig));
#else
  if((unsigned long)thread<8*sizeof(unsigned long long))
    __CPROVER_assume(__CPROVER_threads_exited&(1<<(unsigned long)thread));
#endif
  return 0;
}

/* FUNCTION: pthread_rwlock_destroy */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_destroy(pthread_rwlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(*((signed char *)lock)==0,
    "lock held upon destroy");
  *((signed char *)lock)=-1;
  return 0;
}

/* FUNCTION: pthread_rwlock_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_init(pthread_rwlock_t *lock, 
  const pthread_rwlockattr_t *attr)
{
  __CPROVER_HIDE:;
  (*(signed char *)lock)=0;
  if(attr!=0) (void)*attr;
  return 0;
}

/* FUNCTION: pthread_rwlock_rdlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_rdlock(pthread_rwlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  __CPROVER_assert(*((signed char *)lock)!=-1,
    "lock not initialised or destroyed");
  __CPROVER_assume(!*((signed char *)lock));
  *((signed char *)lock)=1;
  __CPROVER_atomic_end();
  return 0; // we never fail
}

/* FUNCTION: pthread_rwlock_tryrdlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_tryrdlock(pthread_rwlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  if((*(signed char *)lock & 2)!=0) { __CPROVER_atomic_end(); return 1; }
  (*(signed char *)lock)|=1;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_rwlock_trywrlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_trywrlock(pthread_rwlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  if(*(signed char *)lock) { __CPROVER_atomic_end(); return 1; }
  (*(signed char *)lock)=2;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_rwlock_unlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_unlock(pthread_rwlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(*((signed char *)lock)==1,
    "must hold lock upon unlock");
  // TODO: unlocks all held locks at once
  *((signed char *)lock)=0;
  return 0; // we never fail
}

/* FUNCTION: pthread_rwlock_wrlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_rwlock_wrlock(pthread_rwlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  __CPROVER_assert(*((signed char *)lock)!=-1,
    "lock not initialised or destroyed");
  __CPROVER_assume(!*((signed char *)lock));
  *((signed char *)lock)=2;
  __CPROVER_atomic_end();
  return 0; // we never fail
}

/* FUNCTION: pthread_create */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

extern unsigned long long __CPROVER_threads_exited;
extern _Thread_local unsigned long __CPROVER_thread_id;
extern unsigned long __CPROVER_next_thread_id;

// using separate function avoid unnecessary copies of local variables
// (malloc!), don't inline!
void __actual_thread_spawn(
  void * (*start_routine)(void *),
  void *arg,
  unsigned long id)
{
  __CPROVER_HIDE:;
  __CPROVER_ASYNC_1: __CPROVER_thread_id=id,
                       start_routine(arg),
                       __CPROVER_threads_exited|=1<<id;
}

int pthread_create(
  pthread_t *thread,
  const pthread_attr_t *attr,
  void * (*start_routine)(void *),
  void *arg)
{
  __CPROVER_HIDE:;
  unsigned long this_thread_id;
  __CPROVER_atomic_begin();
  this_thread_id=++__CPROVER_next_thread_id;
  __CPROVER_atomic_end();

#ifdef __APPLE__
  if(thread)
  {
    *thread=malloc(sizeof(typeof(**thread)));
    (*thread)->__sig=this_thread_id;
  }
#else
  if(thread) *thread=this_thread_id;
#endif
  if(attr) (void)*attr;
  __actual_thread_spawn(start_routine, arg, this_thread_id);

  return 0;
}

/* FUNCTION: pthread_cond_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_cond_init(
    pthread_cond_t *cond,
    const pthread_condattr_t *attr)
{ __CPROVER_HIDE:
  *((unsigned *)cond)=0;
  if(attr) (void)*attr;
  return 0;
}

/* FUNCTION: pthread_cond_signal */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_cond_signal(
    pthread_cond_t *cond)
{ __CPROVER_HIDE:
  __CPROVER_atomic_begin();
  (*((unsigned *)cond))++;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_cond_broadcast */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_cond_broadcast(
    pthread_cond_t *cond)
{ __CPROVER_HIDE:
  __CPROVER_atomic_begin();
  *((unsigned *)cond)=(unsigned)-1;
  __CPROVER_atomic_end();
  return 0;
}

/* FUNCTION: pthread_cond_wait */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_cond_wait(
    pthread_cond_t *cond,
    pthread_mutex_t *mutex)
{ __CPROVER_HIDE:
  pthread_mutex_unlock(mutex);
  __CPROVER_atomic_begin();
  __CPROVER_assume(*((unsigned *)cond));
  (*((unsigned *)cond))--;
  __CPROVER_atomic_end();
  pthread_mutex_lock(mutex);
  return 0; // we never fail
}

