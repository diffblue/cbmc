// N5008 [temp.inst]/16: the only bound on recursive instantiation is an
// implementation-defined limit on the TOTAL depth (Annex B suggests 1024).
// Checking is_invocable_v<forward_impl, int *> instantiates
// invokable_r<forward_impl, int *>, which (through forward_impl's
// constrained call operator and back_op's trailing return type) needs
// invokable_r<back_op, at, int, int *> and invokable_r<at, int *, int>: three
// different specializations of one class template, nested.  CBMC skipped the
// third as a suspected infinite recursion; the incomplete invoke_of<at, int *,
// int> it left behind then made the later call `c(arr)' fail.  libc++'s
// std::views::take closure (__perfect_forward_impl over __bind_back_op) does
// this.
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
int main()
{
  int arr[1];
  forward_impl<back_op, at, int> c;
  static_assert(is_invocable_v<decltype(c), int *>);
  __CPROVER_assert(c(arr) == 3, "call after the trait");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
