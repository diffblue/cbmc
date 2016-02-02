/* FUNCTION: pthread_mutexattr_settype */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type)
{
  __CPROVER_HIDE:;

  (void)attr;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  if(type==PTHREAD_MUTEX_RECURSIVE)
    __CPROVER_set_must(attr, "mutexattr-recursive");
  #else
  (void)type;
  #endif

  int result;
  return result;
}

/* FUNCTION: pthread_cancel */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_cancel(pthread_t thread)
{
  __CPROVER_HIDE:;

  (void)thread;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(&thread, "pthread-id"),
                   "pthread_cancel must be given valid thread ID");
  #endif

  int result;
  return result;
}

/* FUNCTION: pthread_mutex_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_mutex_t_defined
#define __CPROVER_mutex_t_defined
#if defined __CYGWIN__ || defined __MINGW32__ || defined _WIN32
// on Windows, the mutexes are integers already
typedef pthread_mutex_t __CPROVER_mutex_t;
#else
typedef signed char __CPROVER_mutex_t;
#endif
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
inline void pthread_mutex_cleanup(void *p)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(
    __CPROVER_get_must(p, "mutex-destroyed"),
    "mutex must be destroyed");
}
#endif

inline int pthread_mutex_init(
  pthread_mutex_t *mutex, const pthread_mutexattr_t *mutexattr)
{
  __CPROVER_HIDE:;
  *((__CPROVER_mutex_t *)mutex)=0;
  if(mutexattr!=0) (void)*mutexattr;
  
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_cleanup(mutex, pthread_mutex_cleanup);
  __CPROVER_set_must(mutex, "mutex-init");
  __CPROVER_clear_may(mutex, "mutex-destroyed");
  if(__CPROVER_get_must(mutexattr, "mutexattr-recursive"))
    __CPROVER_set_must(mutex, "mutex-recursive");
  #endif

  return 0;
}

/* FUNCTION: pthread_mutex_lock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_mutex_t_defined
#define __CPROVER_mutex_t_defined
#if defined __CYGWIN__ || defined __MINGW32__ || defined _WIN32
// on Windows, the mutexes are integers already
typedef pthread_mutex_t __CPROVER_mutex_t;
#else
typedef signed char __CPROVER_mutex_t;
#endif
#endif

inline int pthread_mutex_lock(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-init"),
                   "mutex must be initialized");

  __CPROVER_assert(!__CPROVER_get_may(mutex, "mutex-destroyed"),
                   "mutex must not be destroyed");

  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-recursive") ||
                   !__CPROVER_get_may(mutex, "mutex-locked"),
                   "attempt to lock non-recurisive locked mutex");

  __CPROVER_set_must(mutex, "mutex-locked");
  __CPROVER_set_may(mutex, "mutex-locked");

  __CPROVER_assert(*((__CPROVER_mutex_t *)mutex)!=-1,
    "mutex not initialised or destroyed");
  #endif

  __CPROVER_assume(!*((__CPROVER_mutex_t *)mutex));

  *((__CPROVER_mutex_t *)mutex)=1;
  __CPROVER_atomic_end();

  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");

  return 0; // we never fail
}

/* FUNCTION: pthread_mutex_trylock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_mutex_t_defined
#define __CPROVER_mutex_t_defined
#if defined __CYGWIN__ || defined __MINGW32__ || defined _WIN32
// on Windows, the mutexes are integers already
typedef pthread_mutex_t __CPROVER_mutex_t;
#else
typedef signed char __CPROVER_mutex_t;
#endif
#endif

inline int pthread_mutex_trylock(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;
  int return_value;
  __CPROVER_atomic_begin();

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-init"),
                   "mutex must be initialized");

  __CPROVER_assert(*((__CPROVER_mutex_t *)mutex)!=-1,
    "mutex not initialised or destroyed");
  #endif

  if(*((__CPROVER_mutex_t *)mutex)==1)
  {
    // failed
    return_value=1;
  }
  else
  {
    // ok
    return_value=0;
    *((__CPROVER_mutex_t *)mutex)=1;
  }

  __CPROVER_atomic_end();

  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");

  return return_value;
}

/* FUNCTION: pthread_mutex_unlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_mutex_t_defined
#define __CPROVER_mutex_t_defined
#if defined __CYGWIN__ || defined __MINGW32__ || defined _WIN32
// on Windows, the mutexes are integers already
typedef pthread_mutex_t __CPROVER_mutex_t;
#else
typedef signed char __CPROVER_mutex_t;
#endif
#endif

inline int pthread_mutex_unlock(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-init"),
                   "mutex must be initialized");

  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-locked"),
                   "mutex must be locked");

  __CPROVER_assert(!__CPROVER_get_may(mutex, "mutex-destroyed"),
                   "mutex must not be destroyed");

  __CPROVER_clear_may(mutex, "mutex-locked");
  #endif

  // the fence must be before the unlock
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                    "WWcumul", "RRcumul", "RWcumul", "WRcumul");
  __CPROVER_atomic_begin();
  __CPROVER_assert(*((__CPROVER_mutex_t *)mutex)==1,
    "must hold lock upon unlock");
  *((__CPROVER_mutex_t *)mutex)=0;
  __CPROVER_atomic_end();

  return 0; // we never fail
}

/* FUNCTION: pthread_mutex_destroy */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_mutex_t_defined
#define __CPROVER_mutex_t_defined
#if defined __CYGWIN__ || defined __MINGW32__ || defined _WIN32
// on Windows, the mutexes are integers already
typedef pthread_mutex_t __CPROVER_mutex_t;
#else
typedef signed char __CPROVER_mutex_t;
#endif
#endif

inline int pthread_mutex_destroy(pthread_mutex_t *mutex)
{
  __CPROVER_HIDE:;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-init"),
                   "mutex must be initialized");

  __CPROVER_assert(!__CPROVER_get_may(mutex, "mutex-locked"),
                   "mutex must not be locked");

  __CPROVER_assert(!__CPROVER_get_may(mutex, "mutex-destroyed"),
                   "mutex must not be destroyed");

  __CPROVER_set_must(mutex, "mutex-destroyed");
  __CPROVER_set_may(mutex, "mutex-destroyed");
  #endif

  __CPROVER_assert(*((__CPROVER_mutex_t *)mutex)==0,
    "lock held upon destroy");
  *((__CPROVER_mutex_t *)mutex)=-1;

  return 0;
}

/* FUNCTION: pthread_exit */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

extern __CPROVER_bool __CPROVER_threads_exited[];
extern __CPROVER_thread_local unsigned long __CPROVER_thread_id;

inline void pthread_exit(void *value_ptr)
{
  __CPROVER_HIDE:;
  if(value_ptr!=0) (void)*(char*)value_ptr;
  __CPROVER_threads_exited[__CPROVER_thread_id]=1;
  __CPROVER_assume(0);
}

/* FUNCTION: pthread_join */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

extern __CPROVER_bool __CPROVER_threads_exited[];
extern __CPROVER_thread_local unsigned long __CPROVER_thread_id;
extern unsigned long __CPROVER_next_thread_id;

inline int pthread_join(pthread_t thread, void **value_ptr)
{
  __CPROVER_HIDE:;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(&thread, "pthread-id"),
                   "phtread_join must be given valid thread ID");
  #endif

  if((unsigned long)thread>__CPROVER_next_thread_id) return ESRCH;
  if((unsigned long)thread==__CPROVER_thread_id) return EDEADLK;
  if(value_ptr!=0) (void)**(char**)value_ptr;
  __CPROVER_assume(__CPROVER_threads_exited[(unsigned long)thread]);

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
    "rwlock held upon destroy");
  *((signed char *)lock)=-1;
  
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS   
  __CPROVER_set_must(lock, "rwlock_destroyed");
  #endif

  return 0;
}

/* FUNCTION: pthread_rwlock_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS  
inline void pthread_rwlock_cleanup(void *p)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(__CPROVER_get_must(p, "rwlock_destroyed"),
                   "rwlock must be destroyed");
}
#endif

inline int pthread_rwlock_init(pthread_rwlock_t *lock, 
  const pthread_rwlockattr_t *attr)
{
  __CPROVER_HIDE:;
  (*(signed char *)lock)=0;
  if(attr!=0) (void)*attr;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS    
  __CPROVER_cleanup(lock, pthread_rwlock_cleanup);
  #endif

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

extern __CPROVER_bool __CPROVER_threads_exited[];
extern __CPROVER_thread_local unsigned long __CPROVER_thread_id;
extern unsigned long __CPROVER_next_thread_id;

inline int pthread_create(
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
  
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(thread, "pthread-id");
  #endif

  if(thread)
  {
    #ifdef __APPLE__
    // pthread_t is a pointer type on the Mac
    *thread=(pthread_t)this_thread_id;
    #else
    *thread=this_thread_id;
    #endif
  }

  if(attr) (void)*attr;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS    
  // Clear all locked mutexes; locking must happen in same thread.
  __CPROVER_clear_must(0, "mutex-locked");
  __CPROVER_clear_may(0, "mutex-locked");
  #endif
  
  __CPROVER_ASYNC_1:
    __CPROVER_thread_id=this_thread_id,
    start_routine(arg),
    __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                    "WWcumul", "RRcumul", "RWcumul", "WRcumul"),
    __CPROVER_threads_exited[this_thread_id]=1;

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

  (void)*mutex;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-init"),
                   "mutex must be initialized");

  __CPROVER_assert(__CPROVER_get_must(mutex, "mutex-locked"),
                   "mutex must be locked");

  __CPROVER_assert(!__CPROVER_get_may(mutex, "mutex-destroyed"),
                   "mutex must not be destroyed");

  __CPROVER_clear_may(mutex, "mutex-locked");
  #endif

  __CPROVER_atomic_begin();
  __CPROVER_assume(*((unsigned *)cond));
  (*((unsigned *)cond))--;
  __CPROVER_atomic_end();

  return 0; // we never fail
}

/* FUNCTION: pthread_spin_lock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

// no pthread_spinlock_t on the Mac
#ifndef __APPLE__
int pthread_spin_lock(pthread_spinlock_t *lock)
{
  __CPROVER_HIDE:;
  __CPROVER_atomic_begin();
  __CPROVER_assume(!*((unsigned *)lock));
  (*((unsigned *)lock))=1;
  __CPROVER_atomic_end();
  
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");
  return 0;
}
#endif

/* FUNCTION: pthread_spin_unlock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

// no pthread_spinlock_t on the Mac
#ifndef __APPLE__
int pthread_spin_unlock(pthread_spinlock_t *lock)
{
  __CPROVER_HIDE:;
  // This is atomic_full_barrier() in glibc.
  // The fence must be before the unlock.
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");
  *((unsigned *)lock) = 0;
  return 0;
}
#endif

/* FUNCTION: pthread_spin_trylock */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

// no pthread_spinlock_t on the Mac
#ifndef __APPLE__
int pthread_spin_trylock(pthread_spinlock_t *lock)
{
  __CPROVER_HIDE:;
  int result;
  __CPROVER_atomic_begin();
  if(*((unsigned *)lock))
    result=EBUSY;
  else
  {
    result=0;
    (*((unsigned *)lock))=1;
  }
  __CPROVER_atomic_end();
  
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence",
                  "WWcumul", "RRcumul", "RWcumul", "WRcumul");
  return result;
}
#endif

/* FUNCTION: pthread_barrier_init */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_barrier_init(
  pthread_barrier_t *restrict barrier,
  const pthread_barrierattr_t *restrict attr, unsigned count)
{
  __CPROVER_HIDE:;
  (void)barrier;
  (void)attr;
  (void)count;
  
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(barrier, "barrier-init");
  __CPROVER_clear_may(barrier, "barrier-destroyed");
  #endif
  
  int result;
  return result;
}       

/* FUNCTION: pthread_barrier_destroy */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_barrier_destroy(pthread_barrier_t *barrier)
{
  __CPROVER_HIDE:;
  
  (void)barrier;
  
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(barrier, "barrier-init"),
                   "pthread barrier must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(barrier, "barrier-destroyed"),
                   "pthread barrier must not be destroyed");
  __CPROVER_set_may(barrier, "barrier-destroyed");
  #endif

  int result;
  return result;
}

/* FUNCTION: pthread_barrier_wait */

#ifndef __CPROVER_PTHREAD_H_INCLUDED
#include <pthread.h>
#define __CPROVER_PTHREAD_H_INCLUDED
#endif

inline int pthread_barrier_wait(pthread_barrier_t *barrier)
{
  __CPROVER_HIDE:;
  
  (void)barrier;
  
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(barrier, "barrier-init"),
                   "pthread barrier must be initialized");
  __CPROVER_assert(!__CPROVER_get_may(barrier, "barrier-destroyed"),
                   "pthread barrier must not be destroyed");
  #endif

  int result;
  return result;
}
