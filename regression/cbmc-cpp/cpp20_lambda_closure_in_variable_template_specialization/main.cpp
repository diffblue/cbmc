extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.prim.lambda.closure]/1, /4: a lambda in a variable template's
// initializer has a closure type per specialization; its function call
// operator is defined in that specialization, here fits<base<int>::U>
// instantiated from a static member of base<int> (libc++'s
// __fits_in_tail_padding in <expected>)
template <class F>
inline constexpr bool fits = []()
{
  struct x
  {
    F f;
  };
  return sizeof(x) == sizeof(F);
}();
template <class T>
struct base
{
  struct U
  {
    T t;
  };
  static constexpr bool tail = fits<U>;
};
int main()
{
  __CPROVER_assert(base<int>::tail, "closure in variable template");
  __CPROVER_assert(!base<int>::tail, "WRONG (must FAIL)");
  return 0;
}
