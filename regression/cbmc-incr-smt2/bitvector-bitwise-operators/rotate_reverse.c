int main()
{
  // rotate left by constant
  unsigned a;
  __CPROVER_assume(a == 0x12345678u);
  unsigned rl = (a << 8) | (a >> 24);
  __CPROVER_assert(__builtin_rotateleft32(a, 8) == rl, "rotate left by 8");

  // rotate right by constant
  unsigned rr = (a >> 4) | (a << 28);
  __CPROVER_assert(__builtin_rotateright32(a, 4) == rr, "rotate right by 4");

  // rotate by zero
  __CPROVER_assert(
    __builtin_rotateleft32(a, 0) == a, "rotate left by 0 is identity");

  // rotate left by dynamic amount
  unsigned n;
  __CPROVER_assume(n == 16);
  unsigned rl_dyn = (a << 16) | (a >> 16);
  __CPROVER_assert(
    __builtin_rotateleft32(a, n) == rl_dyn, "rotate left by dynamic 16");

  // bitreverse
  unsigned char b;
  __CPROVER_assume(b == 0xB0u); // 10110000
  // reversed: 00001101 = 0x0D
  __CPROVER_assert(
    __builtin_bitreverse8(b) == 0x0Du, "bitreverse of 0xB0 should be 0x0D");
}
