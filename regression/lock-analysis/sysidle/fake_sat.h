#include <stdlib.h>

/* 32-bit build. */

typedef signed char s8;
typedef unsigned char u8;

typedef signed short s16;
typedef unsigned short u16;

typedef signed int s32;
typedef unsigned int u32;

typedef signed long long s64;
typedef unsigned long long u64;

#define USHRT_MAX	((u16)(~0U))
#define SHRT_MAX	((s16)(USHRT_MAX>>1))
#define SHRT_MIN	((s16)(-SHRT_MAX - 1))
#define INT_MAX		((int)(~0U>>1))
#define INT_MIN		(-INT_MAX - 1)
#define UINT_MAX	(~0U)
#define LONG_MAX	((long)(~0UL>>1))
#define LONG_MIN	(-LONG_MAX - 1)
#define ULONG_MAX	(~0UL)
#define LLONG_MAX	((long long)(~0ULL>>1))
#define LLONG_MIN	(-LLONG_MAX - 1)
#define ULLONG_MAX	(~0ULL)
//#define SIZE_MAX	(~(size_t)0)

#define UINT_CMP_GE(a, b)       (UINT_MAX / 2 >= (a) - (b))
#define UINT_CMP_LT(a, b)       (UINT_MAX / 2 < (a) - (b))
#define ULONG_CMP_GE(a, b)      (ULONG_MAX / 2 >= (a) - (b))
#define ULONG_CMP_LT(a, b)      (ULONG_MAX / 2 < (a) - (b))

typedef _Bool                   bool;
#define false 0
#define true  1

#include "atomic_sat.h"

/*
 * Note: no "lock" prefix even on SMP: xchg always implies lock anyway.
 * Since this is generally used to protect other memory information, we
 * use "asm volatile" and "memory" clobbers to prevent gcc from moving
 * information around.
 */
#define xchg(ptr, v)	\
({ \
	__typeof__(*(ptr)) __old; \
	__typeof__(ptr) __ptr; \
	__typeof__(*(ptr)) __v; \
	for (;;) { \
		__old = ACCESS_ONCE(*ptr); \
		if (__sync_val_compare_and_swap(__ptr, __old, __v) == __old) \
			return __old; \
	} \
	__old; \
})

/*
 * Atomic compare and exchange.  Compare OLD with MEM, if identical,
 * store NEW in MEM.  Return the initial value in MEM.  Success is
 * indicated by comparing RETURN with OLD.
 */
#define __raw_cmpxchg(ptr, old, new, size, lock)			\
	__sync_val_compare_and_swap(ptr, old, new)

#define __cmpxchg(ptr, old, new, size)					\
	__raw_cmpxchg((ptr), (old), (new), (size), LOCK_PREFIX)

#define __sync_cmpxchg(ptr, old, new, size)				\
	__raw_cmpxchg((ptr), (old), (new), (size), "lock; ")

#define __cmpxchg_local(ptr, old, new, size)				\
	__raw_cmpxchg((ptr), (old), (new), (size), "")

#include "cmpxchg_32_sat.h"

// #ifdef __HAVE_ARCH_CMPXCHG
#define cmpxchg(ptr, old, new)						\
	__cmpxchg(ptr, old, new, sizeof(*(ptr)))

#define sync_cmpxchg(ptr, old, new)					\
	__sync_cmpxchg(ptr, old, new, sizeof(*(ptr)))

#define cmpxchg_local(ptr, old, new)					\
	__cmpxchg_local(ptr, old, new, sizeof(*(ptr)))
// #endif

/*
 * xadd() adds "inc" to "*ptr" and atomically returns the previous
 * value of "*ptr".
 *
 * xadd() is locked when multiple CPUs are online
 * xadd_sync() is always locked
 * xadd_local() is never locked
 */
#define __xadd(ptr, inc, lock)	__sync_fetch_and_add(ptr, inc)
#define xadd(ptr, inc)		__xadd((ptr), (inc), LOCK_PREFIX)
#define xadd_sync(ptr, inc)	__xadd((ptr), (inc), "lock; ")
#define xadd_local(ptr, inc)	__xadd((ptr), (inc), "")

#define __add(ptr, inc, lock) __sync_fetch_and_add(ptr, inc)

/*
 * add_*() adds "inc" to "*ptr"
 *
 * __add() takes a lock prefix
 * add_smp() is locked when multiple CPUs are online
 * add_sync() is always locked
 */
#define add_smp(ptr, inc)	__add((ptr), (inc), LOCK_PREFIX)
#define add_sync(ptr, inc)	__add((ptr), (inc), "lock; ")

#define barrier() __asm__ __volatile__("": : :"memory")
#define ACCESS_ONCE(x) (*(volatile typeof(x) *)&(x))
#define smp_mb() asm volatile("mfence":::"memory")

#define likely(x) (x)
#define unlikely(x) (x)

void cpu_relax_poll(void)
{
}

void cpu_relax_poll_random(void)
{
}

void (*cpu_relax_func)(void) = cpu_relax_poll;

#define cpu_relax() cpu_relax_func()

int __thread my_smp_processor_id;

#define raw_smp_processor_id() my_smp_processor_id

static inline void cpu_init(int cpu)
{
	my_smp_processor_id = cpu;
}

#define WARN_ON(c) \
	do { \
		if (c) \
			abort(); \
	} while (0)
#define BUG_ON(c) \
	do { \
		if (c) \
			abort(); \
	} while (0)

#define offsetof(TYPE, MEMBER) ((size_t) &((TYPE *)0)->MEMBER)

/**
 * container_of - cast a member of a structure out to the containing structure
 * @ptr:        the pointer to the member.
 * @type:       the type of the container struct this is embedded in.
 * @member:     the name of the member within the struct.
 *
 */
#define container_of(ptr, type, member) ({                      \
	const typeof( ((type *)0)->member ) *__mptr = (ptr);    \
	(type *)( (char *)__mptr - offsetof(type,member) );})

#define __round_mask(x, y) ((__typeof__(x))((y)-1))
#define round_up(x, y) ((((x)-1) | __round_mask(x, y))+1)
#define round_down(x, y) ((x) & ~__round_mask(x, y))

#define FIELD_SIZEOF(t, f) (sizeof(((t*)0)->f))
#define DIV_ROUND_UP(n,d) (((n) + (d) - 1) / (d))
#define DIV_ROUND_UP_ULL(ll,d) \
	({ unsigned long long _tmp = (ll)+(d)-1; do_div(_tmp, d); _tmp; })

#define set_cpus_allowed_ptr(a, b) do { } while (0)

struct rcu_head {
	struct callback_head *next;
	void (*func)(struct callback_head *head);
};

static inline void call_rcu(struct rcu_head *head, void (*func)(struct rcu_head *rcu))
{
	func(head);  /* Don't try this at home!!!  It will normally break. */
}

struct irq_work {
	int a;
};

int __thread my_smp_processor_id;

#define raw_smp_processor_id() my_smp_processor_id
#define smp_processor_id() my_smp_processor_id

#define WARN_ON_ONCE(c) ({ int __c = (c);  if (__c) abort(); c; })

volatile unsigned long jiffies = 0;

typedef int raw_spinlock_t;
#define ____cacheline_internodealigned_in_smp

struct list_head {
	struct list_head *prev;
	struct list_head *next;
};

#define __percpu
#define __init
#define __cpuinit

typedef atomic_t atomic_long_t;
typedef int wait_queue_head_t;

struct mutex {
	int a;
};
struct completion {
	int a;
};

#define DECLARE_PER_CPU(t, n) t

#define cpu_is_offline(c) 0

#define for_each_possible_cpu(cpu) for ((cpu) = 0; (cpu) < nr_cpu_ids; (cpu)++)

#define per_cpu_ptr(p, cpu) (&(p)[cpu])

#define DYNTICK_TASK_NEST_WIDTH 7
#define DYNTICK_TASK_NEST_VALUE ((LLONG_MAX >> DYNTICK_TASK_NEST_WIDTH) + 1)
#define DYNTICK_TASK_NEST_MASK  (LLONG_MAX - DYNTICK_TASK_NEST_VALUE + 1)
#define DYNTICK_TASK_FLAG	   ((DYNTICK_TASK_NEST_VALUE / 8) * 2)
#define DYNTICK_TASK_MASK	   ((DYNTICK_TASK_NEST_VALUE / 8) * 3)
#define DYNTICK_TASK_EXIT_IDLE	   (DYNTICK_TASK_NEST_VALUE + \
				    DYNTICK_TASK_FLAG)
