# Song-encoding soundness reproducer

`song-spurious-unit-min.smt2` is a 3-assert minimisation (via ddmin,
from `Sage2/bench_2155.smt2`, declared `sat`) of the soundness bug
fixed in commit "Item 14: adopt Song et al.'s sound disequality
encoding; fix predicate width bug".

Bug: `extract_predicate` emitted the spurious constant `1` (i.e.
`1 = 0`) for a width-inconsistent signed comparison
(`0 <s x` canonicalised to `x >=s 1`, sign-XOR-transformed to a lower
bound whose constant `2^31+1` exceeded the ring width `d=16`),
poisoning the equality system so the main Gröbner check reported a
spurious UNSAT. Expected: `sat`. Fix: width-consistency guard in
`poly_extract.cpp` (`C >= 2^d` ⇒ defer to bit-blasting).
