extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct rcv
{
  using type = T;
};
template <class T>
struct rcv<T &>
{
  using type = T;
};
template <class T>
struct rcv<T &&>
{
  using type = T;
};
template <class T>
using rcv_t = typename rcv<T>::type;
template <class T>
struct is_mfp
{
  static constexpr bool v = false;
};
template <class R, class C, class... A>
struct is_mfp<R (C::*)(A...)>
{
  static constexpr bool v = true;
};
template <class T>
constexpr bool is_mfp_v = is_mfp<T>::v;
struct inv_functor
{
  template <class C, class... T>
  static auto call(C &&c, T &&...a)
    -> decltype(static_cast<C &&>(c)(static_cast<T &&>(a)...))
  {
    return static_cast<C &&>(c)(static_cast<T &&>(a)...);
  }
};
struct inv_pmf_pointer
{
  template <class D, class T1, class... T2>
  static auto call(D pmf, T1 &&a1, T2 &&...a2)
    -> decltype(((*static_cast<T1 &&>(a1)).*pmf)(static_cast<T2 &&>(a2)...))
  {
    return ((*static_cast<T1 &&>(a1)).*pmf)(static_cast<T2 &&>(a2)...);
  }
};
template <class C, class T1, class R = rcv_t<C>, bool P = is_mfp_v<R>>
struct inv1;
template <class C, class T1, class R>
struct inv1<C, T1, R, true> : inv_pmf_pointer
{
};
template <class C, class T1, class R>
struct inv1<C, T1, R, false> : inv_functor
{
};
// N5008 [temp.variadic]/5, [basic.scope.param]/1: in each specialization the
// trailing return type expands the function parameter pack a2 with that
// specialization's elements (the shape of the MSVC STL's std::invoke)
template <class C, class T1, class... T2>
auto invoke(C &&c, T1 &&a1, T2 &&...a2) -> decltype(inv1<C, T1>::call(
  static_cast<C &&>(c),
  static_cast<T1 &&>(a1),
  static_cast<T2 &&>(a2)...))
{
  return inv1<C, T1>::call(
    static_cast<C &&>(c), static_cast<T1 &&>(a1), static_cast<T2 &&>(a2)...);
}
int add(int a, int b)
{
  return a + b;
}
struct S
{
  int acc = 0;
  void add2(S &s, const int &a)
  {
    s.acc += a;
  }
};
int main()
{
  int r = invoke(add, 1, 2);
  S s;
  invoke(&S::add2, &s, s, 3);
  __CPROVER_assert(r == 3 && s.acc == 3, "both invoked");
  __CPROVER_assert(s.acc == 0, "WRONG (must FAIL)");
  return 0;
}
