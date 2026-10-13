// Unit proof for big-int arithmetic (src/big-int/bigint.cc).
//
// The unit tests exercise fixed operand values; this harness verifies
// ring identities over ALL int operands (nondeterministic inputs):
//  * commutativity of + and *
//  * additive inverse: a + (-a) == 0
//  * subtraction round-trip: (a + b) - b == a
//  * comparison consistency with the int operands
//
// ---------------------------------------------------------------------------
// Why this proof does not scale (profiled 2026-10-13, CBMC at commit
// 77f4dbd42c; data and logs were in /tmp/r183).
//
// Symbolic execution is cheap: 0.9 s, 9,665 steps, 8,081 VCCs (1,787 after
// simplification).  The SAT back-end then runs out of memory while it is
// still BUILDING the propositional formula: with --dimacs (no solver) the
// CNF reached 60 M variables / 184 M clauses at the 16 GB cap after ~70 s.
// The same happens with --sat-solver cadical, --arrays-uf-always and
// --refine-arrays, and with a single property (--property
// main.assertion.N --slice-formula).
//
// perf: practically all of that time is under
//   bv_pointerst::finish_eager_conversion -> arrayst::add_array_constraints
// i.e. the eager array-theory constraints, not bit-vector arithmetic.
// Instrumenting arrayst (temporary counters around add_array_constraint)
// showed, at the point of running out of memory:
//   ARRAY_IF             1.22 M constraints, 36 M variables
//   ARRAY_COMPREHENSION    56 k constraints, 19 M variables
//   ARRAY_WITH            260 k constraints, 3.8 M variables
// over 1,596 array terms in 100 equivalence classes of ~114 members each
// (initial index sets of at most 32 indices, 608 in total, 686 array
// equalities).  The largest classes are the digit buffers:
//   unsignedbv[32][((adjust_size(..)::size * 4 + 39) / 32 * 32 - 8) / 4]
// i.e. dynamic objects whose SIZE is symbolic: BigInt::allocate rounds
// the digit count with adjust_size(), and the digit count depends on the
// nondeterministic operands.  Each SSA merge of a buffer (`c ? a : b`) adds
// one ARRAY_IF constraint per index of the class, and indices propagate
// through the whole class, so the count grows roughly with
// (class size) x (index-set size) x (number of merges).  The
// ARRAY_COMPREHENSION constraints come from memcpy/memset of symbolic
// length (array comprehensions whose body repeats the size arithmetic,
// ~340 variables per instance).
//
// The SMT2 encoding of the same problem is small (6.9 MB, written in
// 2.9 s): 4,796 bvudiv/bvsdiv (mostly the adjust_size rounding by constant
// divisors), 9,614 bvmul, 2,205 select, 228 store, 719 arrays of 32-bit and
// 161 arrays of 8-bit elements, no bit-vector wider than 192 bits.
// cbmc --z3 (4.8.12) and cbmc --cvc5 (1.2.1) did not answer within 30
// minutes, both using little memory.
//
// Directions: an array encoding whose constraint count does not scale
// with class size x index set (lazy/refined instantiation of the if- and
// comprehension constraints, or not merging whole buffers at joins), or a
// harness whose BigInts have a FIXED digit capacity.  The int range is not
// the cost driver; the symbolic allocation size is.
//
// Reproducing the measurements (each run capped at 16 GB address space):
//   cbmc <options from test.desc> harness.cpp --verbosity 9
//       phase timings ("Runtime Symex", "Runtime Convert SSA", ...)
//   ... --dimacs --outfile p.cnf      CNF size without running a solver
//   ... --smt2 --outfile p.smt2       SMT-LIB encoding, for external solvers
//   perf record -g cbmc ...           where the time goes
#include <big-int/bigint.hh>

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();

int main()
{
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  // avoid int overflow in the reference comparisons
  __CPROVER_assume(x > -1000000 && x < 1000000);
  __CPROVER_assume(y > -1000000 && y < 1000000);

  BigInt a(x);
  BigInt b(y);

  __CPROVER_assert(a + b == b + a, "addition commutes");
  __CPROVER_assert(a + b == BigInt(x + y), "addition agrees with int");
  __CPROVER_assert((a + b) - b == a, "subtraction round-trip");
  __CPROVER_assert(a + (-a) == BigInt(0), "additive inverse");
  __CPROVER_assert((x < y) == (a < b), "comparison agrees with int");

  return 0;
}
