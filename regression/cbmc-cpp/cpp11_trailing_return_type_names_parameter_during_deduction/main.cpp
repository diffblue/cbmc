extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [basic.scope.param]/1, [temp.deduct.general]/7: forming the function
// type of the candidate call_binder during deduction substitutes into its
// trailing return type, which names call_binder's own parameter `obj' (the
// MSVC STL's std::_Call_binder, reached when std::function checks that a
// std::bind result is invocable)
template <unsigned long... I>
struct seq
{
};
struct invoker_functor
{
  template <class C, class... T>
  static auto call(C obj, T... args) -> decltype(obj(args...))
  {
    return obj(args...);
  }
};
template <class F, class A1, class... A>
auto invoke(F obj, A1 a1, A... a)
  -> decltype(invoker_functor::call(obj, a1, a...))
{
  return invoker_functor::call(obj, a1, a...);
}
template <class>
struct invoker_ret
{
  template <class F, class... V>
  static auto call(F f, V... v) -> decltype(invoke(f, v...))
  {
    return invoke(f, v...);
  }
};
template <class Ret, unsigned long... I, class F, class Tup>
auto call_binder(Ret, seq<I...>, F obj, Tup) -> decltype(Ret::call(obj, I...))
{
  return Ret::call(obj, I...);
}
long add(long a, long b)
{
  return a + b + 1;
}
template <class R>
struct binder
{
  long (*f)(long, long);
  template <int = 0>
  auto operator()()
  {
    return call_binder(invoker_ret<R>{}, seq<2, 3>{}, f, 0);
  }
};
int main()
{
  binder<int> b{add};
  long r = invoker_functor::call(b);
  __CPROVER_assert(r == 6, "call through binder");
  __CPROVER_assert(r == 5, "WRONG (must FAIL)");
  return 0;
}
