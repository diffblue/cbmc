// N5008 [dcl.spec.auto]/3-4 + [temp.variadic]/4-5: a function template with a
// DEDUCED return type (`auto` / `decltype(auto)`) whose body returns a call
// with a pack expansion, `decltype(auto) impl(seq<I...>) { return add(I...); }`.
// The return type is deduced from the (expanded) return expression.
//
// KNOWNBUG: CBMC leaves such a body incomplete -- "C++ front-end could not
// fully type-check 'main' (unsupported construct)" -- so the call is
// effectively unsound.  A TRAILING return type over the same pack call
// (`-> decltype(add(I...))`) is handled correctly
// (cpp11_decltype_return_nontype_pack_call, CORE); the defect is specific to a
// DEDUCED (`auto` / `decltype(auto)`) return type whose deduction must expand
// the pack-expansion call in the return statement.
//
// This is the remaining layer of cpp17_apply_basic: libstdc++'s std::apply and
// its `__apply_impl` helper both return `decltype(auto)`.  g++ compiles and runs
// r == 3; clang++ accepts.  Flip to CORE once auto-return deduction over a
// pack-expansion call is supported.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <int...>
struct seq
{
};

template <int... I>
decltype(auto) impl(seq<I...>)
{
  return add(I...);
}

int main()
{
  int r = impl(seq<1, 2>{});
  __CPROVER_assert(r == 3, "auto-return pack call yields 3");
  __CPROVER_assert(r != 3, "WRONG must FAIL");
  return 0;
}
