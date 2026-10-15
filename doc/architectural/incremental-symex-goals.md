# Incremental Symex Goal Construction

## Overview

CBMC's standard verification flow runs symbolic execution to completion,
then converts all assertions into a single SAT query. The incremental
goal construction feature allows the SAT solver to be invoked at
intermediate points during symbolic execution, enabling early detection
of property violations and concurrent solver execution.

## Algorithm

The standard `convert_assertions` builds a single disjunction:

    NOT(a1) OR NOT(a2) OR ... OR NOT(aN)

where each `ai` is an assertion condition (under its path assumption).
The solver checks whether any assertion can fail.

The incremental variant (`convert_assertions_incremental`) adds a free
"goal extender" variable `v` to make the disjunction extensible:

    NOT(a1) OR NOT(a2) OR ... OR v

The solver is called with the assumption `NOT(v)`, which effectively
closes the disjunction. On the next call (after more symex steps
produce new assertions), a new clause links to the previous extender:

    NOT(v) OR NOT(a3) OR NOT(a4) OR ... OR v2

With assumption `NOT(v2)`, the solver now checks all assertions from
both batches. The chain of extender variables allows arbitrary
incremental extension without rebuilding earlier clauses.

## Components

### `symex_target_equationt::convert_assertions_incremental`

Core algorithm in `src/goto-symex/symex_target_equation.cpp`. Tracks:
- `current_goal_extender`: the latest extender variable
- `incremental_last_converted`: iterator to resume from
- `incremental_assumption`: accumulated path assumptions

### `periodic_incremental_symex_checker`

In `src/goto-checker/`. Subclasses `symex_bmct` to count symex steps
and pause every N steps (set via `--incremental-check-interval`).
The main loop alternates between symex and solver invocations.

### `concurrent_incremental_symex_checker`

In `src/goto-checker/`. Runs symex in a separate thread. Uses
mutex + condition variable for handoff: symex pauses and sets
`symex_paused=true`, the solver thread processes the equation, then
sets `solver_done=true` to resume symex. The equation is only accessed
by one thread at a time (no concurrent reads/writes).

## Usage

    # Check every 50 symex steps:
    cbmc program.c --incremental-check-interval 50

    # Same, but with concurrent symex and solving:
    cbmc program.c --incremental-check-interval 50 --concurrent-incremental

    # With the existing incremental-loop mode:
    cbmc program.c --incremental-loop main.0 --unwind-max 20

## Limitations

- The incremental check interval is measured in symex steps, not
  assertions. A small interval increases solver overhead; a large
  interval reduces the benefit of early detection.
- The concurrent mode uses a single solver thread. The symex thread
  is blocked while the solver runs (and vice versa), so the speedup
  comes from overlapping symex work with solver work, not from
  parallel solving.
