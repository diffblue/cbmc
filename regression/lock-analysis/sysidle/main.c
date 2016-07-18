#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdarg.h>
#include <time.h>
#include <string.h>
#include "fake_sat.h"

int __unbuffered_cnt = 0;

#define ITER 5

/* uncomment to enable SAT, comment for standard run. */
#define SAT

#define CONFIG_NR_CPUS 2
#define NR_CPUS CONFIG_NR_CPUS
#define CONFIG_RCU_FANOUT 16
#define CONFIG_RCU_FANOUT_LEAF 8

#define CONFIG_NO_HZ_FULL_SYSIDLE
#define CONFIG_NO_HZ_FULL_SYSIDLE_SMALL 4
#define CONFIG_PREEMPT_RCU

#define HZ 1000

int nr_cpu_ids = NR_CPUS;
int rcu_fanout_leaf = CONFIG_RCU_FANOUT_LEAF;

#include "rcutree.h"

struct rcu_state rcu_preempt_state;
struct rcu_state rcu_sched_state;

struct rcu_data rcu_preempt_data_static[CONFIG_NR_CPUS];
struct rcu_data *rcu_preempt_data_array;
struct rcu_data rcu_sched_data_static[CONFIG_NR_CPUS];
struct rcu_data *rcu_sched_data_array;

struct rcu_dynticks rcu_dynticks_static[CONFIG_NR_CPUS];
struct rcu_dynticks *rcu_dynticks_array;

int tick_do_timer_cpu;

void rcu_kick_nohz_cpu(int cpu)
{
	printf("Informed CPU %d of end of full-system idle.\n", cpu);
}

static int rcu_gp_in_progress(struct rcu_state *rsp)
{
	return 0;
}


#include "sysidle.h"

int nthreads = CONFIG_NR_CPUS;

struct thread_arg {
	int me;
};

void do_fqs(struct rcu_state *rsp, struct rcu_data *rdp_in)
{
	int i;
	bool isidle;
	unsigned long maxj;
	int old_full_sysidle_state;
	int new_full_sysidle_state;
	struct rcu_data *rdp;

	/* FQS scan for sched-RCU. */
	isidle = 1;
	maxj = jiffies - ULONG_MAX / 4;
	for (i = 0; i < nthreads; i++) {
		rdp = &rdp_in[i];
		rcu_sysidle_check_cpu(rdp, &isidle, &maxj);
	}
	old_full_sysidle_state = ACCESS_ONCE(full_sysidle_state);
	rcu_sysidle_report(rsp, isidle, maxj, 0);
	new_full_sysidle_state = ACCESS_ONCE(full_sysidle_state);
	if (old_full_sysidle_state != new_full_sysidle_state)
		printf("%lu: System transition from state %d to %d\n",
		       jiffies,
		       old_full_sysidle_state, new_full_sysidle_state);
	old_full_sysidle_state = ACCESS_ONCE(full_sysidle_state);
	if (rcu_sys_is_idle() &&
	    old_full_sysidle_state != RCU_SYSIDLE_FULL_NOTED) {
		printf("%lu: System fully idle\n", jiffies);
	} else {
		new_full_sysidle_state = ACCESS_ONCE(full_sysidle_state);
		if (new_full_sysidle_state != RCU_SYSIDLE_FULL_NOTED &&
		    old_full_sysidle_state != new_full_sysidle_state)
			printf("%lu: System transition from state %d to %d\n",
			       jiffies,
			       old_full_sysidle_state, new_full_sysidle_state);
	}
}

void *timekeeping_cpu(void *arg)
{
	int i;
	struct thread_arg *tap = (struct thread_arg *)arg;

	my_smp_processor_id = tap->me;
	for (i = 0; i < ITER; i++) {
		jiffies++;

		/* FQS scan for RCU-preempt and then RCU-sched. */
		do_fqs(&rcu_preempt_state, rcu_preempt_data_array);
		/* do_fqs(&rcu_sched_state, rcu_sched_data_array); */
	}
	/* asm("sync"); */
	__sync_synchronize();
	__unbuffered_cnt++;
}

void *other_cpu(void *arg)
{
	int i;
	int nest;
	struct rcu_dynticks *rdtp;
	struct thread_arg *tap = (struct thread_arg *)arg;

	my_smp_processor_id = tap->me;
	rdtp = &rcu_dynticks_array[tap->me];
	for (i = 0; i < ITER; i++) {
		/* busy period. */
		WARN_ON_ONCE(full_sysidle_state > RCU_SYSIDLE_LONG);
		WARN_ON_ONCE(full_sysidle_state > RCU_SYSIDLE_LONG);

		/* idle entry. */
		rcu_sysidle_enter(rdtp, 0);

		/* Interrupts from idle. */
		rcu_sysidle_exit(rdtp, 1);
		rcu_sysidle_enter(rdtp, 1);

		/* idle exit. */
		rcu_sysidle_exit(rdtp, 0);
	}
	/* asm("sync"); */
	__sync_synchronize();
	__unbuffered_cnt++;
}

static struct thread_arg ta_array[CONFIG_NR_CPUS+1];

int main(/*int argc, char *argv[]*/)  // argc, argv not used
{
	int i;
	pthread_t tids[CONFIG_NR_CPUS];

	/* Allocate arrays and initialize. */
	rcu_preempt_data_array = rcu_preempt_data_static;
	rcu_sched_data_array = rcu_sched_data_static;
	rcu_dynticks_array = rcu_dynticks_static;
	//memset(rcu_dynticks_array, 0, sizeof(ta_array) * nthreads);
	for (i = 0; i < nthreads; i++) {
		rcu_preempt_data_array[i].dynticks = &rcu_dynticks_array[i];
		rcu_preempt_data_array[i].rsp = &rcu_preempt_state;
		rcu_preempt_data_array[i].cpu = i;
		rcu_sched_data_array[i].dynticks = &rcu_dynticks_array[i];
		rcu_sched_data_array[i].rsp = &rcu_sched_state;
		rcu_sched_data_array[i].cpu = i;
		atomic_set(&rcu_dynticks_array[i].dynticks, 1);
		atomic_set(&rcu_dynticks_array[i].dynticks_idle, 1);
		rcu_dynticks_array[i].dynticks_idle_nesting =
			DYNTICK_TASK_EXIT_IDLE;
		ta_array[i].me = i;
	}
	rcu_preempt_state.rda = rcu_preempt_data_array;
	rcu_sched_state.rda = rcu_sched_data_array;

	/* Stress test. */
#ifdef SAT
	i = 0;
	__CPROVER_ASYNC_0: { timekeeping_cpu(&ta_array[0]); i++; }
	__CPROVER_ASYNC_1: { other_cpu(&ta_array[1]); i++; }
	__CPROVER_ASYNC_2: { other_cpu(&ta_array[2]); i++; }
	__CPROVER_ASYNC_3: { other_cpu(&ta_array[3]); i++; }
	__CPROVER_assume(__unbuffered_cnt == i);
	assert(full_sysidle_state != RCU_SYSIDLE_FULL_NOTED ||
	       (atomic_read(&rcu_preempt_data_array[1].dynticks->dynticks_idle) & 0x1) == 0 &&
	       (atomic_read(&rcu_preempt_data_array[2].dynticks->dynticks_idle) & 0x1) == 0 
          && (atomic_read(&rcu_preempt_data_array[3].dynticks->dynticks_idle) & 0x1) == 0 );
#else /* SAT */
	printf("Start stress test.\n");
	pthread_create(&tids[0], NULL, timekeeping_cpu, &ta_array[0]);
	for (i = 1; i < nthreads; i++) {
		pthread_create(&tids[i], NULL, other_cpu, &ta_array[i]);
	}
	sleep(10);
	for (i = 0; i < nthreads; i++) {
		void *junk;

		if (pthread_join(tids[i], &junk) != 0) {
			perror("pthread_join()");
			abort();
		}
	}
	printf("End of stress test.\n");
#endif /* #else SAT */
}
