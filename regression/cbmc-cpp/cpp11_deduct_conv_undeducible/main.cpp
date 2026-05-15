// [temp.deduct.conv]/1 + [temp.deduct]/8: when the conversion-function
// template's return type does not mention the template parameter,
// deduction cannot determine T, so the template is not a viable
// candidate for an implicit conversion.
//
// Per the standard the only way to invoke the template here is
// with explicit template arguments (e.g., `a.operator<int>()`),
// which is not how implicit conversions work.  Therefore the
// implicit conversion of `any_t` to `int` must fail.

struct any_t
{
  int stored;

  // T is undeducible from the return type, so this template is
  // not a candidate for `int x = a;`.
  template <class T>
  operator int() const
  {
    return stored;
  }
};

int main()
{
  any_t a;
  a.stored = 42;

  int x = a;  // Per [temp.deduct]/8: deduction fails; conversion
              // is rejected.
  (void)x;

  return 0;
}
