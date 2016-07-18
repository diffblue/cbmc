#ifdef CONFIG_NO_HZ_FULL_SYSIDLE

/*
 * Define RCU flavor that holds sysidle state.  This needs to be the
 * most active flavor of RCU.
 */
#ifdef CONFIG_PREEMPT_RCU
static struct rcu_state *rcu_sysidle_state = &rcu_preempt_state;
#else /* #ifdef CONFIG_PREEMPT_RCU */
static struct rcu_state *rcu_sysidle_state = &rcu_sched_state;
#endif /* #else #ifdef CONFIG_PREEMPT_RCU */

static int full_sysidle_state;		/* Current system-idle state. */
#define RCU_SYSIDLE_NOT		0	/* Some CPU is not idle. */
#define RCU_SYSIDLE_SHORT	1	/* All CPUs idle for brief period. */
#define RCU_SYSIDLE_LONG	2	/* All CPUs idle for long enough. */
#define RCU_SYSIDLE_FULL	3	/* All CPUs idle, ready for sysidle. */
#define RCU_SYSIDLE_FULL_NOTED	4	/* Actually entered sysidle state. */

/*
 * Invoked to note exit from irq or task transition to idle.  Note that
 * usermode execution does -not- count as idle here!  After all, we want
 * to detect full-system idle states, not RCU quiescent states and grace
 * periods.  The caller must have disabled interrupts.
 */
static void rcu_sysidle_enter(struct rcu_dynticks *rdtp, int irq)
{
	unsigned long j;

	/* Adjust nesting, check for fully idle. */
	if (irq) {
		rdtp->dynticks_idle_nesting--;
		WARN_ON_ONCE(rdtp->dynticks_idle_nesting < 0);
		if (rdtp->dynticks_idle_nesting != 0)
			return;  /* Still not fully idle. */
	} else {
		if ((rdtp->dynticks_idle_nesting & DYNTICK_TASK_NEST_MASK) ==
		    DYNTICK_TASK_NEST_VALUE) {
			rdtp->dynticks_idle_nesting = 0;
		} else {
			rdtp->dynticks_idle_nesting -= DYNTICK_TASK_NEST_VALUE;
			WARN_ON_ONCE(rdtp->dynticks_idle_nesting < 0);
			return;  /* Still not fully idle. */
		}
	}

	/* Record start of fully idle period. */
	j = jiffies;
	ACCESS_ONCE(rdtp->dynticks_idle_jiffies) = j;
	smp_mb__before_atomic_inc();
	atomic_inc(&rdtp->dynticks_idle);
	smp_mb__after_atomic_inc();
	WARN_ON_ONCE(atomic_read(&rdtp->dynticks_idle) & 0x1);
}

/*
 * Unconditionally force exit from full system-idle state.  This is
 * invoked when a normal CPU exits idle, but must be called separately
 * for the timekeeping CPU (tick_do_timer_cpu).  The reason for this
 * is that the timekeeping CPU is permitted to take scheduling-clock
 * interrupts while the system is in system-idle state, and of course
 * rcu_sysidle_exit() has no way of distinguishing a scheduling-clock
 * interrupt from any other type of interrupt.
 */
void rcu_sysidle_force_exit(void)
{
	int oldstate = ACCESS_ONCE(full_sysidle_state);
	int newoldstate;

	/*
	 * Each pass through the following loop attempts to exit full
	 * system-idle state.  If contention proves to be a problem,
	 * a trylock-based contention tree could be used here.
	 */
	while (oldstate > RCU_SYSIDLE_SHORT) {
		newoldstate = cmpxchg(&full_sysidle_state,
				      oldstate, RCU_SYSIDLE_NOT);
		if (oldstate == newoldstate &&
		    oldstate == RCU_SYSIDLE_FULL_NOTED) {
			rcu_kick_nohz_cpu(tick_do_timer_cpu);
			return; /* We cleared it, done! */
		}
		oldstate = newoldstate;
	}
	smp_mb(); /* Order initial oldstate fetch vs. later non-idle work. */
}

/*
 * Invoked to note entry to irq or task transition from idle.  Note that
 * usermode execution does -not- count as idle here!  The caller must
 * have disabled interrupts.
 */
static void rcu_sysidle_exit(struct rcu_dynticks *rdtp, int irq)
{
	/* Adjust nesting, check for already non-idle. */
	if (irq) {
		rdtp->dynticks_idle_nesting++;
		WARN_ON_ONCE(rdtp->dynticks_idle_nesting <= 0);
		if (rdtp->dynticks_idle_nesting != 1)
			return; /* Already non-idle. */
	} else {
		/*
		 * Allow for irq misnesting.  Yes, it really is possible
		 * to enter an irq handler then never leave it, and maybe
		 * also vice versa.  Handle both possibilities.
		 */
		if (rdtp->dynticks_idle_nesting & DYNTICK_TASK_NEST_MASK) {
			rdtp->dynticks_idle_nesting += DYNTICK_TASK_NEST_VALUE;
			WARN_ON_ONCE(rdtp->dynticks_idle_nesting <= 0);
			return; /* Already non-idle. */
		} else {
			rdtp->dynticks_idle_nesting = DYNTICK_TASK_EXIT_IDLE;
		}
	}

	/* Record end of idle period. */
	smp_mb__before_atomic_inc();
	atomic_inc(&rdtp->dynticks_idle);
	smp_mb__after_atomic_inc();
	WARN_ON_ONCE(!(atomic_read(&rdtp->dynticks_idle) & 0x1));

	/*
	 * If we are the timekeeping CPU, we are permitted to be non-idle
	 * during a system-idle state.  This must be the case, because
	 * the timekeeping CPU has to take scheduling-clock interrupts
	 * during the time that the system is transitioning to full
	 * system-idle state.  This means that the timekeeping CPU must
	 * invoke rcu_sysidle_force_exit() directly if it does anything
	 * more than take a scheduling-clock interrupt.
	 */
	if (smp_processor_id() == tick_do_timer_cpu)
		return;

	/* Update system-idle state: We are clearly no longer fully idle! */
	rcu_sysidle_force_exit();
}

/*
 * Check to see if the current CPU is idle.  Note that usermode execution
 * does not count as idle.  The caller must have disabled interrupts.
 */
static void rcu_sysidle_check_cpu(struct rcu_data *rdp, bool *isidle,
				  unsigned long *maxj)
{
	int cur;
	unsigned long j;
	struct rcu_dynticks *rdtp = rdp->dynticks;

	/*
	 * If some other CPU has already reported non-idle, if this is
	 * not the flavor of RCU that tracks sysidle state, or if this
	 * is an offline or the timekeeping CPU, nothing to do.
	 */
	if (!*isidle || rdp->rsp != rcu_sysidle_state ||
	    cpu_is_offline(rdp->cpu) || rdp->cpu == tick_do_timer_cpu)
		return;
	if (rcu_gp_in_progress(rdp->rsp))
		WARN_ON_ONCE(smp_processor_id() != tick_do_timer_cpu);

	/* Pick up current idle and NMI-nesting counter and check. */
	cur = atomic_read(&rdtp->dynticks_idle);
	if (cur & 0x1) {
		*isidle = false; /* We are not idle! */
		return;
	}
	smp_mb(); /* Read counters before timestamps. */

	/* Pick up timestamps. */
	j = ACCESS_ONCE(rdtp->dynticks_idle_jiffies);
	/* If this CPU entered idle more recently, update maxj timestamp. */
	if (ULONG_CMP_LT(*maxj, j))
		*maxj = j;
}

/*
 * Is this the flavor of RCU that is handling full-system idle?
 */
static bool is_sysidle_rcu_state(struct rcu_state *rsp)
{
	return rsp == rcu_sysidle_state;
}

/*
 * Bind the grace-period kthread for the sysidle flavor of RCU to the
 * timekeeping CPU.
 */
static void rcu_bind_gp_kthread(void)
{
	int cpu = ACCESS_ONCE(tick_do_timer_cpu);

	if (cpu < 0 || cpu >= nr_cpu_ids)
		return;
	if (raw_smp_processor_id() != cpu)
		set_cpus_allowed_ptr(current, cpumask_of(cpu));
}

/*
 * Return a delay in jiffies based on the number of CPUs, rcu_node
 * leaf fanout, and jiffies tick rate.  The idea is to allow larger
 * systems more time to transition to full-idle state in order to
 * avoid the cache thrashing that otherwise occur on the state variable.
 * Really small systems (less than a couple of tens of CPUs) should
 * instead use a single global atomically incremented counter, and later
 * versions of this will automatically reconfigure themselves accordingly.
 */
static unsigned long rcu_sysidle_delay(void)
{
	if (nr_cpu_ids <= CONFIG_NO_HZ_FULL_SYSIDLE_SMALL)
		return 0;
	return DIV_ROUND_UP(nr_cpu_ids * HZ, rcu_fanout_leaf * 1000);
}

/*
 * Advance the full-system-idle state.  This is invoked when all of
 * the non-timekeeping CPUs are idle.
 */
static void rcu_sysidle(unsigned long j)
{
	/* Check the current state. */
	switch (ACCESS_ONCE(full_sysidle_state)) {
	case RCU_SYSIDLE_NOT:

		/* First time all are idle, so note a short idle period. */
		ACCESS_ONCE(full_sysidle_state) = RCU_SYSIDLE_SHORT;
		break;

	case RCU_SYSIDLE_SHORT:

		/*
		 * Idle for a bit, time to advance to next state?
		 * cmpxchg failure means race with non-idle, let them win.
		 */
		if (ULONG_CMP_GE(jiffies, j + rcu_sysidle_delay()))
			(void)cmpxchg(&full_sysidle_state,
				      RCU_SYSIDLE_SHORT, RCU_SYSIDLE_LONG);
		break;

	case RCU_SYSIDLE_LONG:

		/*
		 * Do an additional check pass before advancing to full.
		 * cmpxchg failure means race with non-idle, let them win.
		 */
		if (ULONG_CMP_GE(jiffies, j + rcu_sysidle_delay()))
			(void)cmpxchg(&full_sysidle_state,
				      RCU_SYSIDLE_LONG, RCU_SYSIDLE_FULL);
		break;

	default:
		break;
	}
}

/*
 * Found a non-idle non-timekeeping CPU, so kick the system-idle state
 * back to the beginning.
 */
static void rcu_sysidle_cancel(void)
{
	smp_mb();
	ACCESS_ONCE(full_sysidle_state) = RCU_SYSIDLE_NOT;
}

/*
 * Update the sysidle state based on the results of a force-quiescent-state
 * scan of the CPUs' dyntick-idle state.
 */
static void rcu_sysidle_report(struct rcu_state *rsp, int isidle,
			       unsigned long maxj, bool gpkt)
{
	if (rsp != rcu_sysidle_state)
		return;  /* Wrong flavor, ignore. */
	if (gpkt && nr_cpu_ids <= CONFIG_NO_HZ_FULL_SYSIDLE_SMALL)
		return;  /* Running state machine from timekeeping CPU. */
	if (isidle)
		rcu_sysidle(maxj);    /* More idle! */
	else
		rcu_sysidle_cancel(); /* Idle is over. */
}

/*
 * Wrapper for rcu_sysidle_report() when called from the grace-period
 * kthread's context.
 */
static void rcu_sysidle_report_gp(struct rcu_state *rsp, int isidle,
				  unsigned long maxj)
{
	rcu_sysidle_report(rsp, isidle, maxj, true);
}

/* Callback and function for forcing an RCU grace period. */
struct rcu_sysidle_head {
	struct rcu_head rh;
	int inuse;
};

static void rcu_sysidle_cb(struct rcu_head *rhp)
{
	struct rcu_sysidle_head *rshp;

	/*
	 * The following memory barrier is needed to replace the
	 * memory barriers that would normally be in the memory
	 * allocator.
	 */
	smp_mb();  /* grace period precedes setting inuse. */

	rshp = container_of(rhp, struct rcu_sysidle_head, rh);
	ACCESS_ONCE(rshp->inuse) = 0;
}

/*
 * Check to see if the system is fully idle, other than the timekeeping CPU.
 * The caller must have disabled interrupts.
 */
bool rcu_sys_is_idle(void)
{
	static struct rcu_sysidle_head rsh;
	int rss = ACCESS_ONCE(full_sysidle_state);

	if (WARN_ON_ONCE(smp_processor_id() != tick_do_timer_cpu))
		return false;

	/* Handle small-system case by doing a full scan of CPUs. */
	if (nr_cpu_ids <= CONFIG_NO_HZ_FULL_SYSIDLE_SMALL) {
		int oldrss = rss - 1;

		/*
		 * One pass to advance to each state up to _FULL.
		 * Give up if any pass fails to advance the state.
		 */
		while (rss < RCU_SYSIDLE_FULL && oldrss < rss) {
			int cpu;
			bool isidle = true;
			unsigned long maxj = jiffies - ULONG_MAX / 4;
			struct rcu_data *rdp;

			/* Scan all the CPUs looking for nonidle CPUs. */
			for_each_possible_cpu(cpu) {
				rdp = per_cpu_ptr(rcu_sysidle_state->rda, cpu);
				rcu_sysidle_check_cpu(rdp, &isidle, &maxj);
				if (!isidle)
					break;
			}
			rcu_sysidle_report(rcu_sysidle_state,
					   isidle, maxj, false);
			oldrss = rss;
			rss = ACCESS_ONCE(full_sysidle_state);
		}
	}

	/* If this is the first observation of an idle period, record it. */
	if (rss == RCU_SYSIDLE_FULL) {
		rss = cmpxchg(&full_sysidle_state,
			      RCU_SYSIDLE_FULL, RCU_SYSIDLE_FULL_NOTED);
		return rss == RCU_SYSIDLE_FULL;
	}

	smp_mb(); /* ensure rss load happens before later caller actions. */

	/* If already fully idle, tell the caller (in case of races). */
	if (rss == RCU_SYSIDLE_FULL_NOTED)
		return true;

	/*
	 * If we aren't there yet, and a grace period is not in flight,
	 * initiate a grace period.  Either way, tell the caller that
	 * we are not there yet.  We use an xchg() rather than an assignment
	 * to make up for the memory barriers that would otherwise be
	 * provided by the memory allocator.
	 */
	if (nr_cpu_ids > CONFIG_NO_HZ_FULL_SYSIDLE_SMALL &&
	    !rcu_gp_in_progress(rcu_sysidle_state) &&
	    !rsh.inuse && xchg(&rsh.inuse, 1) == 0)
		call_rcu(&rsh.rh, rcu_sysidle_cb);
	return false;
}

/*
 * Initialize dynticks sysidle state for CPUs coming online.
 */
static void rcu_sysidle_init_percpu_data(struct rcu_dynticks *rdtp)
{
	rdtp->dynticks_idle_nesting = DYNTICK_TASK_NEST_VALUE;
}

#else /* #ifdef CONFIG_NO_HZ_FULL_SYSIDLE */

static void rcu_sysidle_enter(struct rcu_dynticks *rdtp, int irq)
{
}

static void rcu_sysidle_exit(struct rcu_dynticks *rdtp, int irq)
{
}

static void rcu_sysidle_check_cpu(struct rcu_data *rdp, bool *isidle,
				  unsigned long *maxj)
{
}

static bool is_sysidle_rcu_state(struct rcu_state *rsp)
{
	return false;
}

static void rcu_bind_gp_kthread(void)
{
}

static void rcu_sysidle_report_gp(struct rcu_state *rsp, int isidle,
				  unsigned long maxj)
{
}

static void rcu_sysidle_init_percpu_data(struct rcu_dynticks *rdtp)
{
}

#endif /* #else #ifdef CONFIG_NO_HZ_FULL_SYSIDLE */
