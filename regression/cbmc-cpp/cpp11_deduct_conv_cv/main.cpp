// [temp.deduct.conv]/4: when A is cv-qualified, the top-level cv
// is dropped before deduction.  This test verifies that the
// deduction succeeds even when the destination type carries
// top-level const.

struct any_t
{
  int stored;

  template <class T>
  operator T() const
  {
    return T(stored);
  }
};

int main()
{
  any_t a;
  a.stored = 42;

  // `const int` destination: per /4, deduction sees `int`, and
  // T = int.  The conversion succeeds; the resulting `int` is
  // bound to a `const int` lvalue, which is an Exact-Match
  // qualification conversion per [over.ics.user]/3.
  const int as_const_int = a;
  __CPROVER_assert(as_const_int == 42, "deduce T = int via const target");

  return 0;
}
