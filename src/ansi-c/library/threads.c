#ifdef LIBRARY_CHECK
#include <threads.h>
#endif

/* FUNCTION: thrd_create */

// following http://en.cppreference.com/w/c/thread

int thrd_create(thrd_t *thr, thrd_start_t func, void *arg)
{
}

/* FUNCTION: thrd_equal */

int thrd_equal( thrd_t lhs, thrd_t rhs )
{
}

/* FUNCTION: thrd_current */

thrd_t thrd_current()
{
}

/* FUNCTION: thrd_sleep */

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

int mtx_init( mtx_t* mutex, int type )
{
}

/* FUNCTION: mtx_lock */

int mtx_lock(mtx_t* mutex)
{
}

/* FUNCTION: mtx_timedlock */

int mtx_timedlock(mtx_t *restrict mutex,
                  const struct timespec *restrict time_point)
{

}

/* FUNCTION: mtx_trylock */

int mtx_trylock(mtx_t *mutex)
{
}

/* FUNCTION: mtx_unlock */

int mtx_unlock(mtx_t *mutex)
{

}

/* FUNCTION: mtx_destroy */

void mtx_destroy(mtx_t *mutex)
{
}

/* FUNCTION: call_once */

void call_once(once_flag* flag, void (*func)(void))
{
}

/* FUNCTION: cnd_init */

int cnd_init(cnd_t* cond)
{
}

/* FUNCTION: cnd_signal */

int cnd_signal(cnd_t *cond)
{

}

/* FUNCTION: cnd_broadcast */

int cnd_broadcast(cnd_t *cond)
{
}

/* FUNCTION: cnd_wait */

int cnd_wait(cnd_t* cond, mtx_t* mutex)
{
}

/* FUNCTION: cnd_timedwait */

int cnd_timedwait(cnd_t* restrict cond, mtx_t* restrict mutex,
                  const struct timespec* restrict time_point)
{
}

/* FUNCTION: cnd_destroy */

void cnd_destroy(cnd_t* cond)
{
}
