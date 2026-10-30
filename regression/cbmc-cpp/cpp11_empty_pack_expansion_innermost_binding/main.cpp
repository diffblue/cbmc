extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
#include <utility>
// Different templates reuse parameter names, and instantiations nest.  While
// std::pair's converting constructor was being checked,
// `__is_constructible_impl<T, _Args...>' had bound `_Args' to one type;
// std::function's `__result_of_other_impl::_S_test<_Fn, _Args...>', reached
// from there with an EMPTY `_Args', had its `declval<_Args>()...' expanded
// with the OUTER binding (one element): the call got one argument too many,
// `_Callable<F>' came out false and pair<int, std::function<int()>>'s
// constructor lost its body (members never initialised).  N5008
// [basic.scope.scope]: the innermost declaration is the one denoted -- the
// most recently bound pack wins.  The failure was order dependent: any
// earlier std::function<int()> construction in the TU hid it.
int one()
{
  return 1;
}
int take(const std::pair<int, std::function<int()>> &p)
{
  return p.first + p.second();
}
int main()
{
  __CPROVER_assert(
    take({2, one}) == 3,
    "braced list to const pair<int, function>& -- first use of "
    "function<int()>");
  std::pair<int, std::pair<int, std::function<int()>>> s{1, {2, one}};
  __CPROVER_assert(
    s.second.first == 2 && s.second.second() == 1, "nested braces");
  return 0;
}
