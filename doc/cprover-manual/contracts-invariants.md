[CPROVER Manual TOC](../../)

# Invariant Clauses

An _invariant_ clause specifies a property that must be preserved
by every iteration of a loop.
In general a loop has infinitely many invariants.
For instance, `true` is a trivial invariant that holds before the loop,
and after each iteration of the loop (thus, inductive).
However, `true` is rarely useful --
it is an extremely imprecise abstraction of a loop,
which is generally not _sufficient_ to prove any subsequent assertions.

### Syntax

An _invariant_ clause accepts a valid Boolean expression
over the variables visible at the same scope as the loop.
Additionally, [history variables] are also allowed within invariant clauses.

```c
__CPROVER_loop_invariant(bool cond)
```

Invariant clauses may be specified just after the loop guard.
Multiple invariant clauses on the same loop are allowed,
and is equivalent to a single invariant clause that is a conjunction of those clauses.
A few examples are shown below.

```c
while(i < n)
__CPROVER_loop_invariant(0 <= i && i <= n)
{ ... }
```

```c
for(int i = 0; i < n; ++i)
__CPROVER_loop_invariant(0 <= i)
__CPROVER_loop_invariant(i <= n)
{ ... }
```

```c
do { ... }
while (i < n)
__CPROVER_loop_invariant(0 <= i)
__CPROVER_loop_invariant(i <= n);
```

**Important.** Invariant clauses must be free of _side effects_,
for example, mutation of local or global variables.
Otherwise, CBMC raises an error message during compilation:
```
Loop invariant is not side-effect free. (at: file main.c line 4 function main) 
```

### Semantics

A loop invariant clause expands to several assumptions and assertions:
1. The invariant is _asserted_ just before the first iteration.
2. The invariant is _assumed_ on a non-deterministic state to model a non-deterministic iteration.
3. The invariant is finally _asserted_ again to establish its inductiveness.

Mathematical induction is the working principle here.
(1) establishes the base case for induction, and
(2) & (3) establish the inductive case.
Therefore, the invariant must hold _after_ the loop execution for _any_ number of iterations.
The invariant, together with the negation of the loop guard,
must be sufficient to establish subsequent assertions.
If it is not, the abstraction is too imprecise and the user must supply a stronger invariant.

To illustrate the key idea,
consider the following [binary search] loop with invariant clauses:

```c
int binary_search(int val, int *buf, int size)
{
  if(size <= 0 || buf == NULL) return NOT_FOUND;

  long long lb = 0, ub = size - 1;
  long long mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

  while(lb <= ub)
  __CPROVER_loop_invariant(0L <= lb && lb - 1L <= ub && ub < size)
  __CPROVER_loop_invariant(mid == ((unsigned int)lb + (unsigned int)ub) >> 1)
  {
     if(buf[mid] == val) break;
     if(buf[mid] < val)
       lb = mid + 1;
     else
       ub = mid - 1;
     mid = ((unsigned int)lb + (unsigned int)ub) >> 1;
  }
  return lb > ub ? NOT_FOUND : mid;
}
```

The instrumented GOTO program is conceptually similar to the following high-level C program:

```c
int binary_search(int val, int *buf, int size)
{
  if(size <= 0 || buf == NULL) return NOT_FOUND;

  long long lb = 0, ub = size - 1;
  long long mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

  /* 1. assert invariant at loop entry */
  assert(0L <= lb && lb - 1L <= ub && ub < size);
  assert(mid == ((unsigned int)lb + (unsigned int)ub) >> 1);

  /* 2. create a non-deterministic state for modified variables */
  havoc(lb, ub, mid);

  /* 3. establish invariant to model state at an arbitrary iteration */
  __CPROVER_assume(0L <= lb && lb - 1L <= ub && ub < size);
  __CPROVER_assume(mid == ((unsigned int)lb + (unsigned int)ub) >> 1);

  /* 4. perform a single arbitrary iteration (or exit the loop) */
  if(lb <= ub)
  {
    if(buf[mid] == val) break;
    if(buf[mid] < val)
      lb = mid + 1;
    else
      ub = mid - 1;
    mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

    /* 5. assert the invariant to establish inductiveness */
    assert(0L <= lb && lb - 1L <= ub && ub < size);
    assert(mid == ((unsigned int)lb + (unsigned int)ub) >> 1);

    /* 6. terminate this symbolic execution path; similar to "exit" */
    __CPROVER_assume(false);
  }
  return lb > ub ? NOT_FOUND : mid;
}
```

A few things to note here:

- At instrumented code point (2), when we `havoc` the modified variables,
  this set of modified variables is automatically computed
  using alias analysis of l-values appearing in the loop body.
  However, the analysis is incomplete and may fail to characterize the set for complex loops.
  In such cases, the user must manually annotate the set of modified variables
  using an [_assigns clause_](../../contracts/assigns/).

- At instrumented code point (6), when we _assume_ `false`,
  observe that this assumption only exists within the `lb <= ub` conditional.
  Therefore, only the symbolic execution path _inside_ this conditional block terminates.
  The code outside of the conditional block continues to be symbolically executed,
  and subsequent assertions do not become vacuously `true`.

[history variables]: ../../contracts/history-variables/

[binary search]: https://en.wikipedia.org/wiki/Binary_search_algorithm
