extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.variadic]/5: a base-specifier `impl<F, A...>` of a partial
// specialization matched through a FUNCTION-TYPE pattern `RO<F(A...)>` must
// receive every deduced element of A (the shape of libstdc++'s
// `result_of<_Functor(_ArgTypes...)> : __invoke_result<_Functor, _ArgTypes...>`).
template <class F, class... A>
struct impl
{
  typedef int type;
  static constexpr int n = sizeof...(A);
  int m() const { return n; }
};
template <class Sig> struct RO;
template <class F, class... A> struct RO<F(A...)> : public impl<F, A...> {};
// control: the same base clause on a primary template
template <class F, class... A> struct RO2 : public impl<F, A...> {};
using FP = int (*)(int, int);
int main()
{
  RO<FP(int, int)> r;
  __CPROVER_assert(r.m() == 2, "member function through base with pack (function-type pattern)");
  RO2<FP, int, int> r2;
  __CPROVER_assert(r2.m() == 2, "member function through base with pack (plain primary)");
  __CPROVER_assert(RO2<FP, int, int>::n == 2, "static through base (plain primary)");
  __CPROVER_assert(RO<FP(int, int)>::n == 2, "static through base (function-type pattern)");
  __CPROVER_assert(RO<FP &(int &, char &&)>::n == 2, "reference return and parameters");
  RO<FP(int, int)>::type t = 1;
  __CPROVER_assert(t == 1, "typedef through base (function-type pattern)");
  return 0;
}
