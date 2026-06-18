// Header-free reproduction of the type-traits layer that std::__invoke /
// std::invoke_result depend on: a class template computes a member type via a
// decltype whose call expression contains a *pack expansion*
// (decltype(declval<F>()(declval<A>()...))), instantiated with a parameter
// pack, and that member type is used as a function's return type.
//
// KNOWNBUG: the same decltype works inline in a function (or as a trailing
// return type), but when it is the member typedef of a class template
// instantiated with a pack, CBMC computes the wrong type, so the function's
// return value is corrupted.  A trivial member typedef and a decltype without
// pack expansion both work, so the gap is specifically pack expansion inside a
// decltype during class-template instantiation.
//
// This is the remaining gap (after [temp.deduct.call]/3 forwarding-reference
// pack deduction, cpp11_forwarding_ref_pack) behind std::ref'd predicates and
// std::erase_if.  Reclassify CORE once it computes the correct type.

namespace mini
{
template <typename T>
T &&declval() noexcept;

template <typename F, typename... A>
struct invoke_result
{
  typedef decltype(declval<F>()(declval<A>()...)) type;
};

template <typename F, typename... A>
typename invoke_result<F, A...>::type invoke(F f, A... a)
{
  return f(a...);
}
} // namespace mini

template <typename Pred>
int count_matches(const int *first, const int *last, Pred pred)
{
  int n = 0;
  for(; first != last; ++first)
    if(mini::invoke(pred, *first))
      ++n;
  return n;
}

int main()
{
  int a[3] = {1, 2, 3};
  auto pred = [](int x) { return x == 2; };
  __CPROVER_assert(
    count_matches(a, a + 3, pred) == 1,
    "invoke via pack-expansion decltype trait counts 1");
  return 0;
}
