// [temp.deduct.conv]/1: Template arguments for a conversion-function
// template can be deduced by matching the function's return type
// against the destination type of the conversion.  When the
// destination type drives the deduction, deduction can succeed in
// cases where a non-template conversion operator would not match.
//
// This test exercises the simplest variant: a class with a
// `template<class T> operator T() const` template conversion
// operator.  Used in a context that converts to int, the deduction
// instantiates the template with T = int and the conversion
// succeeds.

struct any_t
{
  int stored;

  // Template conversion operator: per [temp.deduct.conv]/1, T is
  // deduced from the destination type at the point of conversion.
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

  // Conversion to int: deduces T = int.
  int as_int = a;
  __CPROVER_assert(as_int == 42, "template conversion-op deduces T = int");

  // Conversion to long: deduces T = long.
  long as_long = a;
  __CPROVER_assert(as_long == 42L, "template conversion-op deduces T = long");

  return 0;
}
