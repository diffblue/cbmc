// N5008 [temp.inst]/16: only the total depth of recursive instantiation is
// bounded.  Checking is_invocable_v<outer<forward_impl<...>>, int *> nests
// four different specializations of invokable_r (outer -> forward_impl ->
// back_op -> at); CBMC's guard against runaway recursion stops at the third
// enclosing instance of one template (elaborate_class_template), so the
// fourth is skipped and the static_assert's evaluation leaves the call
// unusable.  Same mechanism as
// cpp11_nested_instantiations_of_one_class_template, one level deeper.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class If, class>
struct cond
{
  using type = If;
};
template <class T>
T &&declval();
template <class F, class... A>
decltype(F()(A()...)) do_invoke(F, A...);
template <class F, class... A>
struct invokable_r
{
  template <class XF>
  static decltype(do_invoke(XF(), declval<A>()...)) try_call(int);
  using result = decltype(try_call<F>(0));
  static const bool value = true;
};
template <class F, class... A>
struct invoke_of
{
  using type = typename invokable_r<F, A...>::result;
};
template <class F, class... A>
constexpr bool is_invocable_v = invokable_r<F, A...>::value;
struct at
{
  int operator()(int *, int)
  {
    return 3;
  }
};
struct back_op
{
  template <class Fn, class Bound, class A>
  auto operator()(Fn f, Bound b, A a) -> typename invoke_of<Fn, A, int>::type
  {
    return 3;
  }
};
template <class Op, class B1, class B2>
struct forward_impl
{
  template <
    class A,
    class = typename cond<is_invocable_v<Op, B1, B2, A>, int, void>::type>
  auto operator()(A a)
  {
    return Op()(at(), int(), a);
  }
};
template <class Inner>
struct outer
{
  template <
    class A,
    class = typename cond<is_invocable_v<Inner, A>, int, void>::type>
  auto operator()(A a)
  {
    return Inner()(a);
  }
};

int main()
{
  int arr[1];
  forward_impl<back_op, at, int> c;
  outer<forward_impl<back_op, at, int>> o;
  static_assert(is_invocable_v<decltype(o), int *>);
  __CPROVER_assert(o(arr) == 3, "four levels");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
