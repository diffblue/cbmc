// Unit proof for levenshtein_automatont (src/util/edit_distance.cpp).
//
// Verifies over ALL pairs of strings up to length 2 over a two-letter
// alphabet (nondeterministic characters):
//  * reflexivity: get_edit_distance(s, s) == 0 and matches(s);
//  * matches/get_edit_distance consistency: matches(t) iff
//    get_edit_distance(t) has a value (within the error bound);
//  * the reported distance never exceeds the allowed error bound.
// The unit test (unit/util/edit_distance.cpp) spot-checks fixed
// examples; this proves the same properties exhaustively on the
// bounded domain.
// Single translation unit: include the implementation directly.
//
// ---------------------------------------------------------------------------
// Why this proof does not scale (profiled 2026-10-13, CBMC at commit
// 77f4dbd42c; data and logs were in /tmp/r183).
//
// This proof never reaches a decision procedure; symbolic execution does
// not finish (more than 30 minutes, ~2 GB).  --unwind 2: 0.2 s, 5,607
// steps (but the input loop is cut off); --unwind 3 and 4: more than 15
// minutes.  After 300 s at --unwind 6 symex had reached depth ~12,650 --
// the problem is the cost per step, not the number of paths or loop
// iterations (only a few loops are unwound, mostly
// _Hashtable::_M_assign, the copy of a std::unordered_set, and
// _Hashtable_alloc::_M_deallocate_nodes).
//
// perf: the time is in the value-set (points-to) analysis and in irep
// sharing/copying (value_sett::insert/to_expr/get_insert_action,
// sharing_treet::remove_ref/detach, malloc/free).  The NFA's states are
// std::unordered_set<std::size_t>s that are copied repeatedly; every copy
// allocates fresh _Hash_node objects in an unwound loop, and the
// points-to set of a _Hash_node * soon covers all of them: one dereference
// was split over 85 dynamic objects (106 dynamic objects after 300 s),
// giving single assignments of up to 44 KB of text.  The case splits grow
// with every copy.
//
// Directions: a points-to analysis that separates the nodes of different
// hash tables (allocation-site/copy sensitivity), or an NFA with fewer
// copies of its state sets.  The SAT/SMT choice does not matter yet.
//
// Reproducing the measurements (each run capped at 16 GB address space):
//   cbmc <options from test.desc> harness.cpp --verbosity 9
//       phase timings ("Runtime Symex", "Runtime Convert SSA", ...)
//   ... --dimacs --outfile p.cnf      CNF size without running a solver
//   ... --smt2 --outfile p.smt2       SMT-LIB encoding, for external solvers
//   perf record -g cbmc ...           where the time goes
#include <util/edit_distance.h>

#include "../../../src/util/edit_distance.cpp"

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();
char __VERIFIER_nondet_char();

#define MAX_LEN 2

static std::string nondet_string()
{
  int len = __VERIFIER_nondet_int();
  __CPROVER_assume(len >= 0 && len <= MAX_LEN);
  std::string s;
  for(int i = 0; i < len; ++i)
  {
    char c = __VERIFIER_nondet_char();
    __CPROVER_assume(c == 'a' || c == 'b');
    s += c;
  }
  return s;
}

int main()
{
  std::string s = nondet_string();
  std::string t = nondet_string();

  const std::size_t allowed = 1;
  levenshtein_automatont automaton(s, allowed);

  // reflexivity
  auto self_distance = automaton.get_edit_distance(s);
  __CPROVER_assert(
    self_distance.has_value() && *self_distance == 0,
    "distance to itself is zero");
  __CPROVER_assert(automaton.matches(s), "matches itself");

  // consistency + bound
  auto d = automaton.get_edit_distance(t);
  __CPROVER_assert(
    automaton.matches(t) == d.has_value(), "matches iff distance exists");
  if(d.has_value())
    __CPROVER_assert(*d <= allowed, "distance within allowed errors");

  return 0;
}
