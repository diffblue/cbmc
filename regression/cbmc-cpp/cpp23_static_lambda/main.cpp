// N5008 [expr.prim.lambda.general]: the lambda-specifier-seq may contain
// `static' (C++23, P1169): the closure's call operator is a static member
// function -- no `this', so no captures.  Also `constexpr'/`consteval' and
// `mutable' in any order.  MSVC's STL uses `[](_Ty _Val) static { ... }' in
// every language mode (__msvc_bit_utils.hpp, <xstring>).
extern "C" void __CPROVER_assert(bool, const char *);
template <class F>
int apply3(F f)
{
  return f(3);
}
int main()
{
  auto twice = [](int x) static
  {
    return 2 * x;
  };
  __CPROVER_assert(twice(4) == 8, "static lambda");
  __CPROVER_assert(apply3(twice) == 6, "static lambda through a template");
  auto cx = [](int x) static constexpr
  {
    return x + 1;
  };
  __CPROVER_assert(cx(1) == 2, "static constexpr lambda");
  int n = 0;
  auto counter = [n]() mutable { return ++n; };
  __CPROVER_assert(counter() == 1 && counter() == 2, "mutable lambda");
  return 0;
}
