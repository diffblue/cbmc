// KNOWNBUG (header-free reproducer).
//
// N5008 [temp.deduct.call]/3: for a forwarding reference `T&&` and an lvalue
// argument of type A, T is deduced as "lvalue reference to A" (preserving cv-
// qualifiers).  This must work for an enumeration argument just as for any
// other type.
//
// CBMC wrongly rejects a call to `template <typename T> ... f(T&&)` when the
// argument is a `const`-qualified ENUM lvalue ("found no match" ->
// CONVERSION ERROR).  The identical call with a const scalar (e.g. const int),
// or with a non-const enum, resolves correctly -- so the defect is specific to
// deducing/binding a forwarding reference from a const enumeration argument
// (the deduced parameter `const E&` is dropped in overload resolution).
//
// Surfaced (together with the separately-fixed heterogeneous-pack defect
// cpp11_variadic_fwd_ref_heterogeneous) by src/util/validate_expressions.cpp,
// whose `call_on_expr<...>(ns, vm)` forwards a `const validation_modet` (a
// `enum class`) through a forwarding-reference parameter pack.  Flip to CORE
// once a forwarding reference deduces from a const enum argument.

extern "C" void __CPROVER_assert(int, const char *);

enum class mode
{
  a,
  b
};

template <typename T>
int pass(T &&)
{
  return 7;
}

int main()
{
  const mode m = mode::a;
  __CPROVER_assert(pass(m) == 7, "forwarding-ref accepts a const enum lvalue");
  __CPROVER_assert(pass(m) == 9, "WRONG: must fail");
  return 0;
}
