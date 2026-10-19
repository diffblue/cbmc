extern "C" void __CPROVER_assert(bool, const char *);
int twice(int x)
{
  return 2 * x;
}
void takes_array(int (&)[5]);
// N5008 [expr.prim.req.general]/1: the parameters of a requires-expression
// form a parameter-declaration-clause; `int (&a)[5]' and `int (*fp)(int)'
// declare the names a and fp
template <class T>
constexpr bool callable_with_int = requires(T(*fp)(int))
{
  fp(1);
};
int main()
{
  __CPROVER_assert(
    requires(int(&a)[5]) {
      takes_array(a);
      sizeof(a);
    } &&
      requires(int (*fp)(int)) { fp(1); } && callable_with_int<int>,
    "parameters declared");
  __CPROVER_assert(
    !requires(int (*fp)(int)) { fp(1); }, "WRONG (must FAIL)");
  return 0;
}
