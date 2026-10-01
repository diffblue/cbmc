extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct d
{
  typedef T type;
};
// [temp.spec.partial.match]/1, [temp.deduct.type]/10: `R (&)(A...)' matches
// `int (&)(int, int)' with A = {int, int}; [temp.spec.partial.order]: it is
// more specialized than `T &' (the decay shape of libstdc++'s _Bind_helper)
template <class R, class... A>
struct d<R (&)(A...)>
{
  typedef R (*type)(A...);
};
template <class T>
struct d<T &>
{
  typedef T type;
};
// [dcl.ref]/1: `R (*)(B...)' does not match a reference to function
template <class R, class... B>
struct d<R (*)(B...)>
{
  static const int arity = sizeof...(B);
};
int add(int a, int b)
{
  return a + b;
}
int main()
{
  d<int (&)(int, int)>::type p = add;
  __CPROVER_assert(p(1, 2) == 3, "reference to function");
  __CPROVER_assert(d<int (*)(int, int)>::arity == 2, "pointer to function");
  __CPROVER_assert(p(1, 2) != 3, "WRONG (must FAIL)");
}
