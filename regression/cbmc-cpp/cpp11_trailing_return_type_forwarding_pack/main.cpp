extern "C" void __CPROVER_assert(bool, const char *);
// [temp.variadic]/5, [dcl.fct]/8: in the trailing return type the pattern
// static_cast<A &&>(a) is expanded with A_k and the k-th parameter in
// lockstep
template <class... T>
struct tup
{
  static constexpr int n = sizeof...(T);
};
template <class... T>
tup<T...> fat(T &&...);
template <class... A>
auto f(A &&...a) -> decltype(fat(static_cast<A &&>(a)...))
{
  return {};
}
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
int main()
{
  int i = 0;
  __CPROVER_assert(
    same<decltype(f(i, 'c')), tup<int &, char>>::value, "forwarding");
  __CPROVER_assert(decltype(f(i, 'c', 1L))::n == 3, "three elements");
  __CPROVER_assert(
    !same<decltype(f(i, 'c')), tup<int &, char>>::value, "WRONG (must FAIL)");
}
