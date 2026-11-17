// Unit proof for escape (src/util/string_utils.cpp).
//
// escape() prefixes every backslash and double-quote with a backslash.
// The unit-test methodology spot-checks samples; this harness proves,
// over ALL strings up to MAX_LEN from the printable alphabet:
//  * length: |escape(s)| == |s| + #escapable(s)
//  * round-trip: dropping one backslash before each escaped character
//    (the inverse transformation, applied to the char data) yields the
//    original string
//
// ---------------------------------------------------------------------------
// Why this proof does not scale (profiled 2026-10-13, CBMC at commit
// 77f4dbd42c; data and logs were in /tmp/r183).
//
// Symbolic execution is cheap: 1.5 s, 25,696 steps, 5,509 VCCs (1,913 after
// simplification).  The SAT back-end runs out of memory while building
// the formula (~90 s, 15 GB); perf and an instrumented arrayst place the
// cost in the eager array-theory constraints
// (bv_pointerst::finish_eager_conversion -> arrayst::add_array_constraints):
//   ARRAY_IF             2.08 M constraints, 27 M variables
//   ARRAY_WITH            612 k constraints, 4.3 M variables
//   ARRAY_COMPREHENSION   126 k constraints, 8.4 M variables
// over 2,019 array terms in 96 classes (largest: 144 members, 75 indices;
// 778 indices and 669 array equalities in total).  The classes are the
// std::string character buffers, `signedbv[8][dynamic_object_size$N]':
// dynamic objects of SYMBOLIC size, reallocated by `result += c'
// (capacity growth) and copied with memcpy-like comprehensions.
//
// The input length is NOT the cost driver: MAX_LEN 1 costs exactly as much
// as MAX_LEN 3 (same array statistics, same out-of-memory) because
// --unwind 8 bounds the library loops, not the string length.  With
// unwinding assertions, --unwind 4 is the smallest sufficient bound for
// MAX_LEN 3 (unwind 2/3 fail the assertion of the input loop in main) and
// still runs out of memory (14,218 steps, 603 arrays, 13 GB after 87 s);
// so does --unwind 5 (17,048 steps, 882 arrays).
//
// The SMT2 encoding is 50 MB (written in 33 s).  cbmc --z3 did not answer
// within 30 minutes.  cbmc --cvc5 failed to parse CBMC's output: the
// union inside basic_string (its local buffer) was turned back into an
// array as `((as const (Array ..)) ((_ extract 7 0) x))', and cvc5 accepts
// only a VALUE under `as const' (fixed in the SMT2 back-end, see
// regression/cbmc/smt2_cvc5_as_const_value); with the fix cbmc --cvc5
// did not answer within 30 minutes either.
//
// Directions: as for bigint_arith -- the array encoding's constraint
// count for buffers of symbolic size and their SSA merges; a
// capacity-bounded string model; or the smallest sufficient --unwind.
//
// Reproducing the measurements (each run capped at 16 GB address space):
//   cbmc <options from test.desc> harness.cpp --verbosity 9
//       phase timings ("Runtime Symex", "Runtime Convert SSA", ...)
//   ... --dimacs --outfile p.cnf      CNF size without running a solver
//   ... --smt2 --outfile p.smt2       SMT-LIB encoding, for external solvers
//   perf record -g cbmc ...           where the time goes
#include <util/string_utils.h>

// Single translation unit: the front end does not yet merge identical
// inline member definitions across translation units ([basic.def.odr]).
#include "../../../src/util/string_utils.cpp"

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();
char __VERIFIER_nondet_char();

#define MAX_LEN 3

int main()
{
  // bounded-nondet input string
  int len = __VERIFIER_nondet_int();
  __CPROVER_assume(len >= 0 && len <= MAX_LEN);
  char buf[MAX_LEN + 1];
  std::size_t escapable = 0;
  for(int i = 0; i < MAX_LEN; ++i)
  {
    char c = __VERIFIER_nondet_char();
    __CPROVER_assume(c >= 0x20 && c <= 0x7e); // printable
    if(i < len && (c == '\\' || c == '"'))
      escapable++;
    buf[i] = c;
  }
  buf[len] = '\0';
  const std::string input(buf, len);

  const std::string escaped = escape(input);

  __CPROVER_assert(
    escaped.size() == input.size() + escapable, "escaped length");

  // inverse transformation over the char data, without further
  // std::string machinery: skip one backslash before each literal
  std::size_t j = 0;
  bool round_trip = true;
  for(std::size_t i = 0; i < escaped.size() && j <= input.size(); i++)
  {
    char c = escaped[i];
    if(c == '\\' && i + 1 < escaped.size())
      c = escaped[++i]; // escaped literal
    if(j >= input.size() || c != input[j])
    {
      round_trip = false;
      break;
    }
    j++;
  }
  __CPROVER_assert(round_trip && j == input.size(), "unescape round-trip");

  return 0;
}
