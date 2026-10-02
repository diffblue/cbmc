extern "C" void __CPROVER_assert(bool, const char *);
// [temp.deduct.call]/3, [temp.spec.partial.match]: F deduced as a function
// type from `F &', and a typedef of function type, select tr<R(A)>
void cb(int)
{
}
template <class F>
struct tr
{
  static const int v = 0;
};
template <class R, class A>
struct tr<R(A)>
{
  static const int v = 1;
};
template <class R, class A>
struct tr<R (*)(A)>
{
  static const int v = 3;
};
template <class F>
int f(F)
{
  return tr<F>::v;
}
template <class F>
int g(F &)
{
  return tr<F>::v;
}
typedef void T(int);
int main()
{
  __CPROVER_assert(f(cb) == 3, "pointer deduced");
  __CPROVER_assert(g(cb) == 1, "function deduced");
  __CPROVER_assert(tr<T>::v == 1, "typedef");
  __CPROVER_assert(tr<decltype(&cb)>::v == 3, "decltype pointer");
  __CPROVER_assert(g(cb) != 1, "WRONG (must FAIL)");
}
