// std::pair<int, std::function<int()>> p(1, f): the converting constructor
// `pair(_U1 &&, _U2 &&)' is constrained by
// `_PCC::_MoveConstructiblePair<_U1, _U2>()', i.e. by
// is_constructible<function<int()>, int (*&&)()>.  Two things made it false:
// user_defined_conversion_sequence refused nested queries while constructor
// candidates were being explored unless a constant-expression context was
// active (a sfinae_contextt suspends it; N5008 [over.best.ics]/4 speaks of
// the same conversion sequence, not of a nested is_constructible), and the
// two instantiations of function's converting-constructor template,
// `function(int (*const &)())' and `function(int (*&&)())', tied for an
// rvalue argument ([over.ics.rank]/3.2.3: the rvalue-reference binding is
// better).
#include <functional>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
int one()
{
  return 1;
}
int main()
{
  __CPROVER_assert(
    std::is_constructible<std::function<int()>, int (*&&)()>::value,
    "constructible from an rvalue function pointer");
  std::pair<int, std::function<int()>> r(1, one);
  __CPROVER_assert(r.first == 1 && r.second() == 1, "pair(1, one)");
  std::pair<int, std::function<int()>> s(r);
  __CPROVER_assert(s.second() == 1, "copy of the pair");
  return 0;
}
