# Loop Contracts

CBMC offers support for loop contracts, which includes three basic clauses:
- _invariant_ clause for establishing safety properties
- _decreases_ clause for establishing termination, and
- _assigns_ clause for declaring the subset of variables that is modifiable in the loop.

These clauses formally describe an abstraction of a loop for the purpose of a proof.
CBMC also provides a series of built-in constructs
to aid writing loop contracts (e.g., _history variables_ and _quantifiers_).

When a function contract is checked, the tool automatically havocs all static variables
of the program (to start the analysis in an arbitrary state), in the same way
as using `--nondet-static` would do. If one wishes not to havoc some static variables,
then `--nondet-static-exclude name-of-variable` can be used.

## Overview

Consider an implementation of the [binary search algorithm] below.

```c
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>

#define NOT_FOUND (-1)

int binary_search(int val, int *buf, int size)
{
  if(size <= 0 || buf == NULL) return NOT_FOUND;

  int lb = 0, ub = size - 1;
  int mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

  while(lb <= ub)
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

int main() {
  int val, size;
  int *buf = size >= 0 ? malloc(size * sizeof(int)) : NULL;

  int idx = binary_search(val, buf, size);
  if(idx != NOT_FOUND)
    assert(buf[idx] == val);
}
```

The function stores a lower bound `lb` and an upper bound `ub`
initialized to the bounds on the buffer `buf`, i.e., to `0` and `size-1` respectively.
In each iteration, the midpoint `mid` is compared against the target value `val`
and in case of a mismatch either the lower half or the upper half of the buffer is searched recursively.
A developer might be interested in verifying two high-level properties on the loop on all possible buffers `buf` and values `val`:
1. an out-of-bound access should never occur (at `buf[mid]` lookup)
2. the loop must eventually always terminate

To prove the first (memory-safety) property,
we may declare [_loop invariants_](contracts-invariant.md)
that must be preserved across all loop iterations.
In this case, two invariant clauses would together imply that `buf[mid]` lookup is always safe.
The first invariant clause would establish that the bounds (`lb` and `ub`) are always valid:
```c
__CPROVER_loop_invariant(0L <= lb && lb - 1L <= ub && ub < size)
```
Note that in the second conjunct,
the `lb - 1 == ub` case is possible when the value `val` is not found in the buffer `buf`.
The second invariant clause would establish that the midpoint `mid` is always a valid index.
In this particular case we can in fact establish a stronger invariant,
that `mid` is indeed always the midpoint of `lb` and `ub` in every iteration:
```c
__CPROVER_loop_invariant(mid == (lb + ub) / 2L)
```

To prove the second (termination) property,
we may declare a [_decreases clause_](contracts-decreases.md)
that indicates a bounded numeric measure
which must monotonically decrease with each loop iteration.
In this case, it is easy to see that `lb` and `ub` are approaching closer together with each iteration, since either `lb` must increase or `ub` must decrease in each iteration.
```c
__CPROVER_decreases(ub - lb)
```

The loop together with all its contracts is shown below.

```c
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>

#define NOT_FOUND (-1)

int binary_search(int val, int *buf, int size)
{
  if(size <= 0 || buf == NULL) return NOT_FOUND;

  int lb = 0, ub = size - 1;
  int mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

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

int main() {
  int val, size;
  int *buf = size >= 0 ? malloc(size * sizeof(int)) : NULL;

  int idx = binary_search(val, buf, size);
  if(idx != NOT_FOUND)
    assert(buf[idx] == val);
}
```

With CBMC we can now generate an unbounded proof using these contracts:

```sh
goto-cc -o binary_search.goto binary_search.c
goto-instrument --apply-loop-contracts binary_search.goto binary_search_inst.goto
cbmc binary_search_inst.goto --pointer-check --bounds-check --signed-overflow-check
```

The first command compiles the program to a GOTO binary,
next we instrument the loops using the annotated loop contracts,
and finally we verify the instrumented GOTO binary with desired checks.

## Additional Resources

- [Assigns Clause](contracts-assigns.md)
- [Decreases Clause](contracts-decreases.md)
- [History Variables](contracts-history-variables.md)
- [Invariant Clause](contracts-invariant.md)
- [Quantifiers](contracts-quantifiers.md)

[binary search algorithm]: https://en.wikipedia.org/wiki/Binary_search_algorithm
