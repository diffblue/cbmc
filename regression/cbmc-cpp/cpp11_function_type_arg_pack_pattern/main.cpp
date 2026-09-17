extern "C" void __CPROVER_assert(bool, const char *);
template <typename T> struct decay { typedef T type; };
template <typename T> struct decay<T &> { typedef T type; };
template <typename T> struct decay<T &&> { typedef T type; };
template <typename R, typename... A> struct decay<R (&)(A...)> { typedef R (*type)(A...); };
template <typename Sig> struct B;
template <typename F, typename... A>
struct B<F(A...)>
{
  static constexpr int n = sizeof...(A);
  F f;
  int arity() const { return n; }
};
template <bool S, typename F, typename... Bs>
struct helper
{
  typedef typename decay<F>::type ft;
  typedef B<ft(typename decay<Bs>::type...)> type;
};
template <typename F, typename... Bs>
inline typename helper<false, F, Bs...>::type bind(F &&f, Bs &&...bs)
{
  typedef typename helper<false, F, Bs...>::type result;
  result r;
  r.f = f;
  return r;
}
int add(int a, int b) { return a + b; }
int main()
{
  auto b1 = bind(add, 2, 3);
  __CPROVER_assert(b1.arity() == 2, "bind-shaped return type: B<int(*)(int,int)(int,int)>");
  __CPROVER_assert(b1.f(1, 2) == 3, "stored function pointer");
  return 0;
}
