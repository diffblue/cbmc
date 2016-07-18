#ifndef _ASM_X86_ATOMIC_H
#define _ASM_X86_ATOMIC_H


typedef struct {
	int counter;
} atomic_t;

/*
 * Atomic operations that C can't guarantee us.  Useful for
 * resource counting etc..
 */

#define ATOMIC_INIT(i)	{ (i) }

/**
 * atomic_read - read atomic variable
 * @v: pointer of type atomic_t
 *
 * Atomically reads the value of @v.
 */
static inline int atomic_read(const atomic_t *v)
{
	return (*(volatile int *)&(v)->counter);
}

/**
 * atomic_set - set atomic variable
 * @v: pointer of type atomic_t
 * @i: required value
 *
 * Atomically sets the value of @v to @i.
 */
static inline void atomic_set(atomic_t *v, int j)
{
	v->counter = j;
}

/**
 * atomic_add - add integer to atomic variable
 * @i: integer value to add
 * @v: pointer of type atomic_t
 *
 * Atomically adds @i to @v.
 */
static inline void atomic_add(int i, atomic_t *v)
{
	__sync_fetch_and_add(&v->counter, i);
}

/**
 * atomic_sub - subtract integer from atomic variable
 * @i: integer value to subtract
 * @v: pointer of type atomic_t
 *
 * Atomically subtracts @i from @v.
 */
static inline void atomic_sub(int i, atomic_t *v)
{
	atomic_add(-i, v);
}

/**
 * atomic_sub_and_test - subtract value from variable and test result
 * @i: integer value to subtract
 * @v: pointer of type atomic_t
 *
 * Atomically subtracts @i from @v and returns
 * true if the result is zero, or false for all
 * other cases.
 */
static inline int atomic_sub_and_test(int i, atomic_t *v)
{
	return __sync_sub_and_fetch(&v->counter, i) == 0;
}

/**
 * atomic_inc - increment atomic variable
 * @v: pointer of type atomic_t
 *
 * Atomically increments @v by 1.
 */
static inline void atomic_inc(atomic_t *v)
{
	atomic_add(1, v);
}

/**
 * atomic_dec - decrement atomic variable
 * @v: pointer of type atomic_t
 *
 * Atomically decrements @v by 1.
 */
static inline void atomic_dec(atomic_t *v)
{
	atomic_sub(1, v);
}

/**
 * atomic_dec_and_test - decrement and test
 * @v: pointer of type atomic_t
 *
 * Atomically decrements @v by 1 and
 * returns true if the result is 0, or false for all other
 * cases.
 */
static inline int atomic_dec_and_test(atomic_t *v)
{
	return __sync_sub_and_fetch(&v->counter, 1) == 0;
}

/**
 * atomic_inc_and_test - increment and test
 * @v: pointer of type atomic_t
 *
 * Atomically increments @v by 1
 * and returns true if the result is zero, or false for all
 * other cases.
 */
static inline int atomic_inc_and_test(atomic_t *v)
{
	return __sync_add_and_fetch(&v->counter, 1) == 0;
}

/**
 * atomic_add_negative - add and test if negative
 * @i: integer value to add
 * @v: pointer of type atomic_t
 *
 * Atomically adds @i to @v and returns true
 * if the result is negative, or false when
 * result is greater than or equal to zero.
 */
static inline int atomic_add_negative(int i, atomic_t *v)
{
	return __sync_add_and_fetch(&v->counter, i) < 0;
}

/**
 * atomic_add_return - add integer and return
 * @i: integer value to add
 * @v: pointer of type atomic_t
 *
 * Atomically adds @i to @v and returns @i + @v
 */
static inline int atomic_add_return(int i, atomic_t *v)
{
	return __sync_add_and_fetch(&v->counter, i);
}

/**
 * atomic_sub_return - subtract integer and return
 * @v: pointer of type atomic_t
 * @i: integer value to subtract
 *
 * Atomically subtracts @i from @v and returns @v - @i
 */
static inline int atomic_sub_return(int i, atomic_t *v)
{
	return atomic_add_return(-i, v);
}

#define atomic_inc_return(v)  (atomic_add_return(1, v))
#define atomic_dec_return(v)  (atomic_sub_return(1, v))

static inline int atomic_cmpxchg(atomic_t *v, int old, int new)
{
	return __sync_val_compare_and_swap(&v->counter, old, new) == old;
}

static inline int atomic_xchg(atomic_t *v, int new)
{
	int old;

	for (;;) {
		old = atomic_read(v);
		if (__sync_val_compare_and_swap(&v->counter, old, new) == old)
			return old;
	}
}

/**
 * __atomic_add_unless - add unless the number is already a given value
 * @v: pointer of type atomic_t
 * @a: the amount to add to v...
 * @u: ...unless v is equal to u.
 *
 * Atomically adds @a to @v, so long as @v was not already @u.
 * Returns the old value of @v.
 */
static inline int __atomic_add_unless(atomic_t *v, int a, int u)
{
	int c, old;
	c = atomic_read(v);
	for (;;) {
		if (c == (u))
			break;
		old = atomic_cmpxchg((v), c, c + (a));
		if (old == c)
			break;
		c = old;
	}
	return c;
}

/**
 * atomic_inc_short - increment of a short integer
 * @v: pointer to type int
 *
 * Atomically adds 1 to @v
 * Returns the new value of @u
 */
static inline short int atomic_inc_short(short int *v)
{
	__sync_fetch_and_add(v, 1);
}

#ifdef CONFIG_X86_64
/**
 * atomic_or_long - OR of two long integers
 * @v1: pointer to type unsigned long
 * @v2: pointer to type unsigned long
 *
 * Atomically ORs @v1 and @v2
 * Returns the result of the OR
 */
static inline void atomic_or_long(unsigned long *v1, unsigned long v2)
{
	__sync_fetch_and_or(v1, v2);
}
#endif

/* These are x86-specific, used by some header files */
#define atomic_clear_mask(mask, addr)				\
	__sync_fetch_and_and(addr, mask)

#define atomic_set_mask(mask, addr)				\
	__sync_fetch_and_or(addr, mask)

/* Atomic operations are already serializing on x86 */
#define smp_mb__before_atomic_dec()	barrier()
#define smp_mb__after_atomic_dec()	barrier()
#define smp_mb__before_atomic_inc()	barrier()
#define smp_mb__after_atomic_inc()	barrier()

// #ifdef CONFIG_X86_32
// # include <asm/atomic64_32.h>
// #else
// # include <asm/atomic64_64.h>
// #endif

#endif /* _ASM_X86_ATOMIC_H */
