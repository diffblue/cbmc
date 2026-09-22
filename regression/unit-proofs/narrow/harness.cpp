// Unit proof for src/util/narrow.h: over ALL inputs, narrow_cast truncates
// like a static_cast, narrow<> accepts exactly the representable values, and
// narrow_or_throw_out_of_range throws for exactly the others.
#include <util/narrow.h>

#include <stdexcept>

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
long __VERIFIER_nondet_long();

int main()
{
  const long v = __VERIFIER_nondet_long();
  const bool fits = v >= -128 && v <= 127;

  __CPROVER_assert(
    narrow_cast<signed char>(v) == static_cast<signed char>(v),
    "narrow_cast is static_cast");

  bool threw = false;
  signed char r = 0;
  try
  {
    r = narrow_or_throw_out_of_range<signed char>(v);
  }
  catch(const std::out_of_range &)
  {
    threw = true;
  }
  __CPROVER_assert(
    threw == !fits, "throws exactly when the value does not fit");
  __CPROVER_assert(threw || r == v, "the narrowed value is the input");

  if(fits)
  {
    // narrow's INVARIANT holds for a representable value
    __CPROVER_assert(
      narrow<signed char>(v) == v, "narrow preserves a representable value");
  }
  return 0;
}
