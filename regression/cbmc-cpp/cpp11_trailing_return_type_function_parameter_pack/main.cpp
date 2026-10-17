extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
struct tup
{
  static constexpr int n = sizeof...(T);
};
template <class... T>
tup<T...> fat(T...);
// a constructor template whose pack is also named A, instantiated with A
// empty
struct S
{
  template <class... A>
  S(A... a)
  {
  }
};
// [temp.variadic]/5, [dcl.fct]/8: the function parameter pack expansion
// `a...' in the trailing return type has one element per argument (a
// constructor template with a pack of the same name, instantiated empty,
// must not shadow it, [basic.scope.temp]/2)
template <class... A>
auto f(A... a) -> decltype(fat(a...))
{
  S s;
  return {};
}
int main()
{
  __CPROVER_assert(decltype(f(1))::n == 1, "one element");
  __CPROVER_assert(decltype(f(1, 'c'))::n == 2, "two elements");
  __CPROVER_assert(decltype(f())::n == 0, "empty");
  __CPROVER_assert(decltype(f(1))::n != 1, "WRONG (must FAIL)");
}
