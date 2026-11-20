extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [basic.scope.temp]/2, [temp.alias]/2: in the alias template
// enable_if_t, `B' names its template parameter; the namespace-scope alias
// B declared later does not take part.  Substituting into functor::call's
// trailing return type calls binder's operator() template, whose default
// template argument uses enable_if_t; the call is valid and R2 is int.
template <bool, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;
template <class T>
T &&declval();
template <class... T>
struct tuple
{
};
template <class F, class Tup, class = void>
constexpr bool can_call = false;
template <class F, class A>
constexpr bool
  can_call<F, tuple<A>, decltype(void(declval<F &>()(declval<A>())))> = true;
struct functor
{
  template <class C, class... Ts>
  static constexpr auto call(C &&obj, Ts &&...args)
    -> decltype(static_cast<C &&>(obj)(static_cast<Ts &&>(args)...))
  {
    return static_cast<C &&>(obj)(static_cast<Ts &&>(args)...);
  }
};
int add1(int a)
{
  return a + 1;
}
template <class Fd>
struct binder
{
  Fd f;
  template <class... U, enable_if_t<can_call<Fd, tuple<U &&...>>, int> = 0>
  decltype(auto) operator()(U &&...u)
  {
    return f(static_cast<U &&>(u)...);
  }
};
using B = binder<int (*)(int)>;
using R2 = decltype(functor::call(declval<B &>(), declval<int>()));
int main()
{
  B b{add1};
  R2 r = functor::call(b, 4);
  __CPROVER_assert(r == 5, "call");
  __CPROVER_assert(r == 6, "WRONG (must FAIL)");
}