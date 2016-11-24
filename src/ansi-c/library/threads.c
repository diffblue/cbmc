/* FUNCTION: thrd_create */

// following http://en.cppreference.com/w/c/thread

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int thrd_create(thrd_t *thr, thrd_start_t func, void *arg)
{
}

/* FUNCTION: thrd_equal */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int thrd_equal( thrd_t lhs, thrd_t rhs )
{
}

/* FUNCTION: thrd_current */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

thrd_t thrd_current()
{
}

/* FUNCTION: thrd_sleep */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int thrd_sleep(const struct timespec* time_point,
               struct timespec* remaining)
{
}

/* FUNCTION: thrd_yield */

void thrd_yield()
{
}

/* FUNCTION: thrd_exit */

void thrd_exit(int res)
{
  __CPROVER_assume(0);
}

/* FUNCTION: mtx_init */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int mtx_init( mtx_t* mutex, int type )
{
}

/* FUNCTION: mtx_lock */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int mtx_lock(mtx_t* mutex)
{
}

/* FUNCTION: mtx_timedlock */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int mtx_timedlock(mtx_t *restrict mutex,
                  const struct timespec *restrict time_point)
{

}

/* FUNCTION: mtx_trylock */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int mtx_trylock(mtx_t *mutex)
{
}

/* FUNCTION: mtx_unlock */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int mtx_unlock(mtx_t *mutex)
{

}

/* FUNCTION: mtx_destroy */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

void mtx_destroy(mtx_t *mutex)
{
}

/* FUNCTION: call_once */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

void call_once(once_flag* flag, void (*func)(void))
{
}

/* FUNCTION: cnd_init */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int cnd_init(cnd_t* cond)
{
}

/* FUNCTION: cnd_signal */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int cnd_signal(cnd_t *cond)
{

}

/* FUNCTION: cnd_broadcast */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int cnd_broadcast(cnd_t *cond)
{
}

/* FUNCTION: cnd_wait */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int cnd_wait(cnd_t* cond, mtx_t* mutex)
{
}

/* FUNCTION: cnd_timedwait */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

int cnd_timedwait(cnd_t* restrict cond, mtx_t* restrict mutex,
                  const struct timespec* restrict time_point)
{
}

/* FUNCTION: cnd_destroy */

#ifndef __CPROVER_THREADS_H_INCLUDED
#include <threads.h>
#define __CPROVER_THREADS_H_INCLUDED
#endif

void cnd_destroy(cnd_t* cond)
{
}

