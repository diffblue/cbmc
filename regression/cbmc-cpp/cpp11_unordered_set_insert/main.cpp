// N5008 [temp.inst]/4: a member function of a class template
// specialization is implicitly instantiated when odr-used.
// unordered_set's insert taking a value is provided by the
// std::__detail::_Insert CRTP mixin base; the call below odr-uses
// _Insert<...>::insert(value_type&&), which must therefore be
// instantiated.
//
// KNOWNBUG: the front end never instantiates that mixin member's body
// ("no body for callee std::__detail::_Insert<...>::insert"), so the
// element is never inserted and count() returns 0.
//
// g++/clang++ verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);
#include <unordered_set>

int main()
{
  std::unordered_set<int> s;
  s.insert(1);
  __CPROVER_assert(s.count(1) == 1, "inserted element is found");
  __CPROVER_assert(s.count(2) == 0, "absent element is not found");
  return 0;
}
