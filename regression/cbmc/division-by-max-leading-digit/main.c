typedef unsigned __CPROVER_bitvector[128] u128;
typedef signed __CPROVER_bitvector[128] s128;

int main()
{
  // The divisor has two 32-bit digits, the most significant of which is
  // 0xffffffff, and the dividend does not fit into 64 bits.
  u128 a = ((u128)1 << 104) + 5;
  u128 b = 0xffffffffffffffffull;
  __CPROVER_assert(a / b == (u128)1 << 40, "unsigned quotient");
  __CPROVER_assert(a % b == ((u128)1 << 40) + 5, "unsigned remainder");

  s128 c = -(s128)a;
  s128 d = -(s128)b;
  __CPROVER_assert(c / d == (s128)1 << 40, "signed quotient");
  __CPROVER_assert(c % d == -(((s128)1 << 40) + 5), "signed remainder");

  return 0;
}
