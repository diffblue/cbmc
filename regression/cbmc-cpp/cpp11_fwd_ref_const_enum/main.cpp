// Header-free regression test.
//
// N5008 [temp.deduct.call]/3: for a forwarding reference `T&&` and an lvalue
// argument of type A, T is deduced as "lvalue reference to A" (preserving cv-
// qualifiers).  This must work for an enumeration argument just as for any
// other type, so a const enum argument yields a `const E&` parameter.
//
// CBMC used to reject a call to `template <typename T> ... f(T&&)` when the
// argument was a `const`-qualified ENUM lvalue ("found no match" ->
// CONVERSION ERROR): the deduced `const E&` parameter had its const dropped by
// cpp_convert_plain_type, which (unlike for struct_tag/union_tag) routed a
// `c_enum_tag` through the general conversion path that rebuilds the type and
// loses cv-qualifiers, so the parameter became a non-const `E&` that the const
// enum lvalue could not bind.  Fixed by treating `c_enum_tag` as a tag
// reference (left untouched) like `struct_tag`/`union_tag`.
//
// Surfaced (together with the heterogeneous-pack defect
// cpp11_variadic_fwd_ref_heterogeneous) by src/util/validate_expressions.cpp,
// whose `call_on_expr<...>(ns, vm)` forwards a `const validation_modet` (a
// `enum class`) through a forwarding-reference parameter pack.

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
