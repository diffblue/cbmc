int main()
{
  unsigned a;

  // popcount
  __CPROVER_assume(a == 0xF0);
  __CPROVER_assert(__builtin_popcount(a) == 4, "popcount of 0xF0 should be 4");

  // count leading zeros (32-bit)
  unsigned b;
  __CPROVER_assume(b == 0x00800000u);
  __CPROVER_assert(__builtin_clz(b) == 8, "clz of 0x00800000 should be 8");

  // count trailing zeros
  unsigned c;
  __CPROVER_assume(c == 0x00800000u);
  __CPROVER_assert(__builtin_ctz(c) == 23, "ctz of 0x00800000 should be 23");

  // find first set (1-indexed from LSB)
  unsigned d;
  __CPROVER_assume(d == 0x00800000u);
  __CPROVER_assert(__builtin_ffs(d) == 24, "ffs of 0x00800000 should be 24");

  // ffs of zero
  __CPROVER_assert(__builtin_ffs(0) == 0, "ffs of 0 should be 0");
}
