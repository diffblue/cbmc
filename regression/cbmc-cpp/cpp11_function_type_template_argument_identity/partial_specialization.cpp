extern "C" void __CPROVER_assert(bool, const char *);
// [temp.spec.partial.match], [temp.deduct.type]/8: a function type argument
// matches the partial specializations for function types, written or
// obtained through decltype
void cb(int)
{
}
int cc(int &, const char *)
{
  return 0;
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
template <class R, class... A>
struct tr<R(int &, A...)>
{
  static const int v = 2;
};
int main()
{
  __CPROVER_assert(tr<decltype(cb)>::v == 1, "decltype unary");
  __CPROVER_assert(tr<void(int)>::v == 1, "written unary");
  __CPROVER_assert(tr<decltype(cc)>::v == 2, "decltype pack");
  __CPROVER_assert(tr<int(int &, const char *)>::v == 2, "written pack");
  __CPROVER_assert(tr<decltype(cb)>::v != 1, "WRONG (must FAIL)");
}
