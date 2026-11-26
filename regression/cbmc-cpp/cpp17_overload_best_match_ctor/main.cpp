// Regression: overload resolution among multiple converting
// constructors should pick the best-ranked candidate per
// [over.match.best], not bail out as ambiguous on the first
// non-exact second match.
//
// Reduced from dog-fooding goto-cc on
// src/util/fixedbv.cpp:34, which calls
//   power(2, spec.get_fraction_bits())
// where `power` is `mp_integer power(const mp_integer&, const
// mp_integer&)` (mp_integer = BigInt) and BigInt has overloaded
// constructors for int / unsigned / long signed / long unsigned.
// CBMC previously rejected the call as
//   found no match for symbol 'power'
// because user_defined_conversion_sequence treated *any* second
// viable converting constructor as ambiguous, even when one
// candidate was strictly better-ranked.

class BigInt
{
public:
  BigInt()
  {
  }
  BigInt(int)
  {
  }
  BigInt(unsigned)
  {
  }
  BigInt(long signed int)
  {
  }
  BigInt(long unsigned int)
  {
  }
};

BigInt power(const BigInt &base, const BigInt &exp)
{
  return BigInt{};
}

int main()
{
  unsigned long bits = 10;
  power(2, bits); // int -> BigInt and unsigned long -> BigInt
                  // each has a unique best ctor in the overload set
  return 0;
}
