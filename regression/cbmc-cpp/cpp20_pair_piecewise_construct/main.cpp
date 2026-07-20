// N5008 [pairs.pair], [temp.variadic]/5: piecewise pair construction.
// The delegating constructor pair(piecewise_construct_t,
// tuple<_Args1...>, tuple<_Args2...>) delegates to the
// _Index_tuple-tagged constructor whose mem-initializer
// `first(std::forward<_Args1>(std::get<_Indexes1>(__tuple1))...)`
// expands TWO packs (a type pack and a non-type index pack) in
// lockstep, and `second(...)` expands two EMPTY packs
// (value-initialization).
//
// This used to fail: the instantiated mem-initializer kept the raw
// pack names and the ellipsis (only single-element struct_tag type
// packs were substituted), its conversion threw, the constructor was
// silently dropped, and the constructed pair was havocked -- the last
// layer of std::map's operator[] value loss.
//
// g++/clang++ accept and verify at runtime.
#include <tuple>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::pair<const int, int> p(
    std::piecewise_construct, std::forward_as_tuple(1), std::tuple<>());
  __CPROVER_assert(p.first == 1, "first from tuple");
  __CPROVER_assert(p.second == 0, "second value-initialized");
  return 0;
}
