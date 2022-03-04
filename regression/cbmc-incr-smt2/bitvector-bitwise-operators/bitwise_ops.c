int main()
{
  int a;
  int b;

  __CPROVER_assume(a != 0);

  // This is going to be failing for values of `0000` and `1111` (as an example),
  // as the bitwise-& of that will produce 0, failing this assertion.
  __CPROVER_assert(a & b, "This is going to fail for bit-opposites");
  // This will always be true, because bitwise-or allows a 1 at a bit
  // that either A or B have set as one, and with an assumption of
  // a != 0, there's always going to be at least 1 bit set, allowing
  // the assertion below to evaluate to true.
  __CPROVER_assert(a | b, "This is going to hold for all values != 0");
  // This will fail for the same value, as an XOR of the bits will
  // result in `0`, resulting in the assertion failure.
  __CPROVER_assert(
    a ^ b, "This is going to fail for the same value in A and B");
  // This will fail for the exact same value of A and B, as
  // NOT(A) will flip all the bits, resulting in the equality
  // below to be false for the assertion.
  __CPROVER_assert(~a == b, "This will fail for the the same value in A and B");
}
