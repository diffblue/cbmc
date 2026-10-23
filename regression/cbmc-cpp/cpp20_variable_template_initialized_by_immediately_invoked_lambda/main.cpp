extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.prim.lambda.closure]/5: the function call operator of a
// lambda is a constexpr function when it is constexpr-suitable, so a
// variable template initialized by an immediately invoked lambda is usable
// as a template argument ([temp.arg.nontype]/1, libc++'s
// __fits_in_tail_padding in <expected>)
template <class F, class S>
inline constexpr bool fits = []()
{
  struct x
  {
    F f;
    S s;
  };
  return sizeof(x) == sizeof(F);
}();
template <bool B, class T>
struct cond;
template <class T>
struct cond<true, T>
{
  T v;
  static constexpr int tag = 1;
};
template <class T>
struct cond<false, T>
{
  T v;
  static constexpr int tag = 2;
};
template <class T>
struct base
{
  static constexpr bool tail = fits<T, bool>;
  cond<tail, T> r;
};
struct padded
{
  int i;
  char c;
};
int main()
{
  base<int> b;
  b.r.v = 3;
  __CPROVER_assert(decltype(b.r)::tag == 2 && b.r.v == 3, "int has no tail");
  __CPROVER_assert(base<long long>::tail == false, "long long");
  __CPROVER_assert(decltype(b.r)::tag == 1, "WRONG (must FAIL)");
  return 0;
}
