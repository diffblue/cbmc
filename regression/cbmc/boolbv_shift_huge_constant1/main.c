unsigned nondet_unsigned(void);

int main(void)
{
  unsigned x = nondet_unsigned();
  __CPROVER_assume(x != 0);
  // These shifts are UB in C but have defined semantics in the CBMC IR:
  // shifting by at least the width zeros out all bits.
  unsigned r1 = x << 2147483648ULL; // 2^31
  unsigned r2 = x << 4294967296ULL; // 2^32
  __CPROVER_assert(r1 == 0, "shift by 2^31 shifts all bits out");
  __CPROVER_assert(r2 == 0, "shift by 2^32 shifts all bits out");
  return 0;
}
