extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.deduct.call]/1, [temp.arg.explicit]/4, [dcl.spec.auto.general]/
// 12: get<1>(tt) deduces the trailing pack T from tup<int, int>; that holds
// also when the body of a function with a deduced return type is
// instantiated to form a type at namespace scope (std::is_invocable_v over
// a std::bind result of the MSVC STL, whose _Binder::operator() returns
// decltype(auto))
template <class... T>
struct tup
{
};
template <unsigned long N, class... T>
int get(tup<T...> &)
{
  return static_cast<int>(N + sizeof...(T));
}
tup<int, int> tt;
auto gg()
{
  return get<1>(tt);
}
using R = decltype(gg());
R r = gg();
int main()
{
  __CPROVER_assert(r == 3, "namespace-scope type");
  __CPROVER_assert(r == 2, "WRONG (must FAIL)");
  return 0;
}
