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
