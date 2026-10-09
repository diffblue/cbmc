extern "C" void __CPROVER_assert(bool, const char *);
template <class F1, class F2>
void if_else(bool c, F1 f1, F2 f2)
{
  if(c)
    f1();
  else
    f2();
}
template <class T>
struct vec
{
  T val;
  int n;
  template <class... Args>
  void slow_path(Args &&...args)
  {
    val = (args + ...);
    n = 2;
  }
  template <class... Args>
  void fast_path(Args &&...args)
  {
    val = (args + ...);
    n = 1;
  }
  template <class... Args>
  void emplace(bool has_cap, Args &&...args)
  {
    // N5008 [class.mfct.non.static]/3 + [expr.prim.lambda.capture]/8:
    // the unqualified member call names (*this).fast_path -- `this`
    // of the ENCLOSING object, implicitly captured by [&].
    if_else(
      has_cap,
      [&] { fast_path(static_cast<Args &&>(args)...); },
      [&] { slow_path(static_cast<Args &&>(args)...); });
  }
};
int main()
{
  vec<int> v;
  v.n = 0;
  v.emplace(false, 7);
  __CPROVER_assert(v.n == 2 && v.val == 7, "slow path via lambda");
  v.emplace(true, 3);
  __CPROVER_assert(v.n == 1 && v.val == 3, "fast path via lambda");
  return 0;
}
