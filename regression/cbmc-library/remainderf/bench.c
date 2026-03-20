// Benchmark for remainderf: symbolic inputs, used to measure formula
// size and solver performance of the FMA-based remainder implementation.
//
// Performance comparison (concrete UNSAT tests, Ubuntu 24.04):
//
//   remainderf (float):
//     FMA:      18,987 vars,  81,799 clauses, MiniSat ~0.071s
//     ExtPrec:  18,806 vars,  79,472 clauses, MiniSat ~0.067s
//     Delta:    +1.0% vars, +2.9% clauses, +5% time
//
//   remainder (double):
//     FMA:      53,049 vars, 252,604 clauses, MiniSat ~0.233s
//     ExtPrec:  50,246 vars, 233,273 clauses, MiniSat ~0.210s
//     Delta:    +5.6% vars, +8.3% clauses, +11% time
//
// The FMA approach is slightly larger due to the double-width
// multiplication, but the overhead is modest and the correctness
// guarantee (machine-checked Coq proof) is significantly stronger.
//
// Performance comparison on _Float16 (fully symbolic, all finite inputs):
//
//   Approach       | Variables | Clauses | MiniSat(s) | Correct?
//   ---------------|-----------|---------|------------|----------
//   ExtPrec (+3b)  |    12,937 |  52,835 |     0.064  | NO (1)
//   FMA-only       |    14,879 |  61,797 |     0.255  | NO (2)
//   Int-fmod + FMA |    16,461 |  70,497 |     3.340  | YES
//
//   (1) Extended precision: the +3 extra fraction bits are insufficient
//       to distinguish the two remainder candidates at tie-breaking
//       boundaries. Counterexample: x=0.001832, y=-5.364e-7 (|x/y|=3415).
//   (2) FMA-only: when |x/y| overflows the float format, fp_div returns
//       infinity and the remainder is NaN. Counterexample: x=-0.563,
//       y=2.563e-6 (|x/y|=219660 > _Float16 max 65504).
//
// For single-precision float, the Int-fmod formula has ~194K variables
// and times out with MiniSat. The SMT FPA back-end (fp.rem) handles
// all formats efficiently.

#include <assert.h>
#include <math.h>

int main()
{
  float x, y;
  __CPROVER_assume(!__CPROVER_isnanf(x) && !__CPROVER_isinff(x));
  __CPROVER_assume(!__CPROVER_isnanf(y) && !__CPROVER_isinff(y));
  __CPROVER_assume(y != 0.0f);
  float r = remainderf(x, y);
  // IEEE 754: |remainder| <= |y|/2
  assert(r == 0.0f || fabsf(r) <= fabsf(y) / 2.0f);
}
