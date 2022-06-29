[CPROVER Manual TOC](../../)

# Decreases Clauses

A _decreases_ clause specifies a measure that must strictly decrease at every iteration of a loop.
By demonstrating that the measure

1. is bounded from below, and
2. strictly decreases at each iteration

we can prove termination of loops.
This is because the measure must eventually hit the lower bound
at which point the loop must terminate,
since the measure cannot strictly decrease further.
This technique for proving termination was proposed by Robert Floyd,
and interested readers may refer to his seminal paper
"[_Assigning Meaning to Programs_](https://people.eecs.berkeley.edu/~necula/Papers/FloydMeaning.pdf)".

### Syntax

A one-dimensional (1D) decreases clause for a loop is an arithmetic expression `e`
over the variables visible at the same scope as the loop,
specified as `__CPROVER_decreases(e)`.

Like invariant clauses, decreases clauses may be specified just after the loop guard.
An example of a 1D decreases clause is shown below.

```c
for(int i = 0; i < n; i += 2)
__CPROVER_loop_invariant(0 <= i && i <= n)
__CPROVER_decreases(n - i)
{ ... }
```

Please see the [invariant clauses](../../contracts/invariants/) page
for more examples on `for` and `do...while` loops.

To help prove termination of more complex loops,
CBMC also supports multi-dimensional decreases clauses.
A multi-dimensional decreases clause is an [ordered tuple](https://en.wikipedia.org/wiki/Tuple)
of arithmetic expressions, specified as `__CPROVER_decreases(e_1, e_2, ..., e_n)`.
An example of a multi-dimensional decreases clause is given below.

```c
while(i < n)
__CPROVER_loop_invariant(0 <= i && i <= n)
__CPROVER_loop_invariant(0 <= j && j <= n)
__CPROVER_decreases(n - i, n - j)
{
  if (j < n)
    j++;
  else
  {
    i++;
    j = 0;
  }
}
```

We extend the strict arithmetic comparison for 1D decreases clauses
to a strict [lexicographic comparison](https://en.wikipedia.org/wiki/Lexicographic_order)
for multi-dimensional decreases clauses.

**Important.**
Like invariant clauses, decreases clauses must be free of side effects,
for example, mutation of local or global variables.
Otherwise, CBMC raises an error message during compilation:
```
Decreases clause is not side-effect free. (at: file main.c line 4 function main) 
```

### Semantics

A decreases clause extends the loop abstraction introduced in the [invariants clause](../../contracts/invariants/) manual.
In addition to the inductiveness check asserted at the end of a single arbitrary iteration,
CBMC would also assert the strict decrement of the measure specified in the decreases clause.
At a high level, in addition to the assumptions and assertions introduced by the invariant clause,
a decreases clause expands to three key steps:
1. At the beginning of the loop body, record the initial value of the measure specified in the decreases clause.
2. At the end of the loop body, record the final value of the measure specified in the decreases clause.
3. After the loop iteration, assert that the final value is strictly smaller than the initial one.

For a 1D decreases clause, we use the strict arithmetic comparison (i.e., `<`).
For a multi-dimensional decreases clause, say `(e_1, ..., e_n)`,
we extend the strict arithmetic comparison to a strict lexicographic comparison.

As an example, consider our binary search implementation again,
this time with a decreases clause annotation to prove its termination:

```c
int binary_search(int val, int *buf, int size)
{
  if(size <= 0 || buf == NULL) return NOT_FOUND;

  long long lb = 0, ub = size - 1;
  long long mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

  while(lb <= ub)
  __CPROVER_loop_invariant(0L <= lb && lb - 1L <= ub && ub < size)
  __CPROVER_loop_invariant(mid == ((unsigned int)lb + (unsigned int)ub) >> 1)
  __CPROVER_decreases(ub - lb)
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
    /* 5. declare variables for tracking the loop variant */
    int old_measure, new_measure;

    /* 6. evaluate the variant at the start of the loop body */
    old_measure = ub - lb;

    if(buf[mid] == val) break;
    if(buf[mid] < val)
      lb = mid + 1;
    else
      ub = mid - 1;
    mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

    /* 7. assert the invariant to establish inductiveness */
    assert(0L <= lb && lb - 1L <= ub && ub < size);
    assert(mid == ((unsigned int)lb + (unsigned int)ub) >> 1);

    /* 8. evaluate the variant at the end of the loop body */
    new_measure = ub - lb;

    /* 9. assert the decreases clause */
    assert(new_measure < old_measure);

    /* 10. terminate this symbolic execution path; similar to "exit" */
    __CPROVER_assume(false);
  }
  return lb > ub ? NOT_FOUND : mid;
}
```

The instrumented code points (5), (6), (8), and (9) are specific to the decreases clause.

**Important.** 
Decreases clauses work in conjunction with [loop invariants](../../contracts/invariants/),
which model an arbitrary loop iteration at which the decreases clause is checked.
If a decreases clause is annotated on a loop without an invariant clause,
then the weakest possible invariant (i.e, `true`) is used to model an arbitrary iteration.
