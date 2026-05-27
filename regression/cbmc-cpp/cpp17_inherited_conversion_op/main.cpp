// Tests that an inherited user-defined conversion operator
// (`operator bool()`) is found by the implicit-conversion code.
// Mirrors libstdc++'s `__and_<...>` whose `operator bool()` is
// inherited from `integral_constant<bool, V>`.
//
// Pre-fix: `user_defined_conversion_sequence` skipped any
// component with `from_base=true` when looking for cast
// operators.  Per [class.member.lookup]/4 +
// [class.conv.fct]/1, conversion operators inherited from base
// classes ARE valid candidates in derived-class lookup
// (subject to access checks); the early-skip filtered them out
// silently and produced "invalid implicit conversion from
// 'struct X' to 'bool'" at any user of `__and_<...>{}`.

struct base_with_bool
{
  operator bool() const
  {
    return true;
  }
};

struct derived : base_with_bool
{
};

int main()
{
  derived x;
  bool b = x;
  __CPROVER_assert(b, "inherited operator bool found and applied");
  return 0;
}
