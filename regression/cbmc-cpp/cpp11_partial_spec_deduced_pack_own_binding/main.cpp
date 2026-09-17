extern "C" void __CPROVER_assert(bool, const char *);
template <class T> T &&declval() noexcept;
template <class T> struct success { typedef T type; };
template <class A, class B> struct same { static constexpr bool value = false; };
template <class A> struct same<A, A> { static constexpr bool value = true; };
struct other_impl
{
  template <class Fn, class... Args>
  static success<decltype(declval<Fn>()(declval<Args>()...))> _S_test(int);
};
template <bool, class F, class... A> struct impl { typedef void type; };
template <class F, class... A>
struct impl<false, F, A...> : private other_impl
{
  typedef decltype(_S_test<F, A...>(0)) type;
};
template <class F, class... A>
struct invoke_result : public impl<false, F, A...>::type {};
using LFP = long (*)(int);
using FP2 = int (*)(int, int);
int main()
{
  __CPROVER_assert(same<invoke_result<LFP &, int &>::type, long>::value, "first: long");
  __CPROVER_assert(same<invoke_result<FP2 &, int &, int &>::type, int>::value, "second: int (not the first instance's long)");
  __CPROVER_assert(same<impl<false, FP2 &, int &, int &>::type, success<int>>::value, "impl<...>::type of the second is success<int>");
  return 0;
}
