// N5008 [temp.variadic]/5 + [temp.deduct]/2: a heterogeneous parameter
// pack (int*, int) forwarded through the libc++ __invoke /
// __invokable_r / invoke_result_t chain -- `declval<XA>()...` inside a
// static member's decltype, then `declval<A>()...` inside __invoke's
// trailing return -- must keep its element list intact.  CBMC drops
// main here: resolving __invoke's `operator()` finds no match, because
// the pack that reaches the inner decltype has its second element
// replaced by the first (round-62 reduction of the libc++ ranges pipe
// showed invoke_result_t<F,int*,int> becoming __invoke_of<F,int*,int*>).
// 27 lines; g++ and clang++ both accept (-Werror) and run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> T &&declval();
struct fn
{
  int operator()(int *p, int n)
  {
    return p[0] + n;
  }
};
template <class F, class... A>
decltype(declval<F>()(declval<A>()...)) __invoke(F, A &&...);
template <class, class F, class... A> struct invokable_r
{
  template <class XF, class... XA>
  static decltype(__invoke(declval<XF>(), declval<XA>()...)) try_call(int);
  using result = decltype(try_call<F, A...>(0));
};
template <class F, class... A>
using invoke_result_t = typename invokable_r<void, F, A...>::result;
template <class F, class... A> invoke_result_t<F, A...> invoke(F f, A &&...a)
{
  return f(static_cast<A &&>(a)...);
}
int main()
{
  int arr[1]{4};
  // heterogeneous (int*, int): the bleed duplicated element 1 into slot 2
  __CPROVER_assert(invoke(fn{}, arr, 3) == 7, "no pack bleed in invoke chain");
  return 0;
}
