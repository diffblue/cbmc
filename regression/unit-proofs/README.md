# Unit proofs

Proof harnesses that accompany CBMC's unit tests, applying CBMC to its
own code base: where a unit test checks a fixed set of sample inputs, a
unit proof verifies the same contract over *all* inputs in a bounded
domain, constructed nondeterministically and constrained with
`__CPROVER_assume`.

Harness pattern:

```c++
int x = __VERIFIER_nondet_int();
__CPROVER_assume(/* bound the domain */);
/* call the unit under proof */
__CPROVER_assert(/* the property the unit test spot-checks */, "...");
```

Run like any regression suite:

```
../test.pl -p -c /path/to/cbmc
```

Notes:
- Harnesses include the implementation under proof either as an extra
  source file on the options line or via a direct `#include` of the
  `.cpp` (single translation unit) where multi-TU linking of inline
  members is not yet supported.
- Entries marked KNOWNBUG document which front-end defect or scaling
  limit blocks them; they double as tracking tests for those issues.
