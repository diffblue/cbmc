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
