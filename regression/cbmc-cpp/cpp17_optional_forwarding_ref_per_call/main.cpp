// C++17: a class template's forwarding-reference converting constructor
// (the canonical case is std::optional<T>'s `optional(_Up&&)`) must be
// re-deduced per call from the argument's value category
// ([temp.deduct.call]/3), and overload resolution must rank by the
// quality of the argument conversion sequence before falling back to
// the non-template / fewer-template-argument tie-breaker
// ([over.match.best]/1, [over.ics.rank]).
//
// This was order-dependent.  Constructing an optional<S> from an
// *lvalue* S first instantiates the converting constructor with
// `_Up = S&` (parameter `S&`).  When a later construction from a
// *prvalue* S then needs `_Up = S` (parameter `S&&`), two defects
// combined to pick the wrong constructor:
//
//   (a) The user-defined-conversion-sequence component loop trialled
//       the cached `optional(S&)` specialisation and *hard-errored*
//       binding the prvalue to the non-const lvalue reference `S&`,
//       instead of treating that candidate as non-viable
//       ([over.match.viable]) and moving on.
//
//   (b) Once the candidate was correctly excluded and the converting
//       constructor template was re-deduced to `optional(S&&)`, the
//       overload ranking still preferred the copy constructor
//       `optional(const optional<S>&)` — whose argument needs a
//       *second* user-defined conversion S -> optional<S>
//       ([over.best.ics] forbids chaining two user-defined
//       conversions) — because a non-template candidate was ranked
//       ahead of a template one regardless of conversion quality.
//
// With both fixed, the prvalue construction selects the converting
// constructor `optional(S&&)` (an rvalue-reference parameter), while
// the lvalue construction keeps using `optional(S&)`.
//
// Verified at the goto-program level (full std::optional BMC exceeds
// symex memory limits): the prvalue construction must call the
// rvalue-reference converting constructor and there must be no
// conversion error.

#include <optional>

struct S
{
  int x;
  S(int);
  S(const S &);
  S(S &&);
};

S mk();

std::optional<S> from_lvalue(S &s)
{
  return s; // uses optional(S&)
}

std::optional<S> from_prvalue()
{
  return mk(); // must re-deduce optional(S&&), not reuse optional(S&)
}

int main()
{
  return from_prvalue().has_value() ? 0 : 1;
}
